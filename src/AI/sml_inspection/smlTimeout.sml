(* ========================================================================== *)
(* FILE          : smlTimeout.sml                                             *)
(* DESCRIPTION   : Timing out PolyML functions.                               *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure smlTimeout :> smlTimeout =
struct

open HolKernel Abbrev boolLib aiLib Thread

val ERR = mk_HOL_ERR "smlTimeout"

(* -------------------------------------------------------------------------
   Interrupt a thread and wait for it to terminate to continue.
   ------------------------------------------------------------------------- *)

fun interruptkill worker =
  let
    val delay = Time.fromReal 0.01
    fun loop n =
      if not (Thread.isActive worker) then () else
        if n > 0
        then
          (OS.Process.sleep delay; loop (n-1))
        else
          (Feedback.HOL_WARNING "smlTimeout" "interruptkill"
             "thread did not stop after interrupt; terminating it";
           Thread.kill worker handle Thread _ => ())
  in
    Thread.interrupt worker handle Thread _ => ();
    loop 100
  end

(* -------------------------------------------------------------------------
   Timeout with busy main thread
   ------------------------------------------------------------------------- *)

exception FunctionTimeout

datatype 'a result = Res of 'a | Exn of exn

fun capture f x = Res (f x)
  handle Interrupt => raise Interrupt | e => Exn e

fun release (Res y) = y
  | release (Exn x) = raise x

val attrib_async = [Thread.InterruptState Thread.InterruptAsynch,
  Thread.EnableBroadcastInterrupt true]

val attrib_sync = [Thread.InterruptState Thread.InterruptSynch,
  Thread.EnableBroadcastInterrupt true]

(* [wait (c, m) finished] blocks on [c], with [m] held, until the worker
   has signalled (then true: [finished ()] holds) or its time is up
   (then false). *)
fun timeLimit wait f x =
  let
    val m = Mutex.mutex ()
    val curattrib = Thread.getAttributes ()
    val _ = Thread.setAttributes attrib_sync
    val _ = Mutex.lock m
    val c = ConditionVar.conditionVar ()
    val resultref = ref NONE
    fun worker_fun () =
      (
      resultref := SOME (capture f x);
      Thread.setAttributes attrib_sync;
      Mutex.lock m; ConditionVar.signal c; Mutex.unlock m
      )
    val worker = Thread.fork (worker_fun, attrib_async)
    (* An interrupt of the waiting thread must not leave the worker
       running: waitUntil re-locks m before raising it. *)
    val b = wait (c, m) (fn () => Option.isSome (!resultref))
      handle Interrupt =>
        (Mutex.unlock m; Thread.setAttributes curattrib;
         interruptkill worker; raise Interrupt)
    val _ = Mutex.unlock m
    val _ = Thread.setAttributes curattrib
    val _ = if b then () else interruptkill worker
    val result = case !resultref of
        NONE => Exn FunctionTimeout
      | SOME (Exn Interrupt) => Exn FunctionTimeout
      | SOME s => s
  in
    release result
  end

(* the deadline counts from after the worker is forked, so that setting
   it up is not charged to the call *)
fun timeout t f x =
  let val t = Time.fromReal t in
    timeLimit (fn (c, m) => fn _ =>
                 ConditionVar.waitUntil (c, m, Time.now () + t))
      f x
  end

(* -------------------------------------------------------------------------
   Timeout on the CPU time of the thread running the call.  Linux reports
   a thread's CPU time in /proc/<pid>/task/<tid>/stat, fields 14 and 15
   (utime and stime), in ticks of 1/100 s (USER_HZ, 100 on every
   architecture); a thread finds its own file through the
   /proc/thread-self link.
   ------------------------------------------------------------------------- *)

fun thread_stat_file () =
  SOME ("/proc/" ^ OS.FileSys.readLink "/proc/thread-self" ^ "/stat")
  handle OS.SysErr _ => NONE

fun unreadable file cause =
  raise IO.Io {name = file, function = "stat_ticks", cause = cause}

(* The worker reads its own stat file while the timeout may interrupt it:
   interrupts are deferred while the file is open, so that an interrupt
   cannot leave it open. *)
fun read_closed file =
  let
    val saved = Thread.getAttributes ()
    val _ = Thread.setAttributes [Thread.InterruptState Thread.InterruptDefer]
    fun read () =
      let
        val stream = TextIO.openIn file
        val text = TextIO.inputAll stream
          handle e => (TextIO.closeIn stream; raise e)
      in
        TextIO.closeIn stream; text
      end
    val result = Res (read ()) handle e => Exn e
  in
    Thread.setAttributes saved; release result
  end

(* the thread's CPU time, utime + stime, in ticks; a record that cannot
   be read or parsed raises IO.Io *)
fun stat_ticks file =
  let
    val text = read_closed file
    (* field 2, the command name, is in parentheses and may hold spaces *)
    val (_, rest) = Substring.splitr (fn c => c <> #")") (Substring.full text)
    val fields = String.tokens Char.isSpace (Substring.string rest)
    fun field n = valOf (Int.fromString (List.nth (fields, n - 3)))
  in
    field 14 + field 15
  end
  handle e as OS.SysErr _ => unreadable file e
       | e as Subscript => unreadable file e
       | e as Option => unreadable file e

(* Where the call's clock comes from: nothing yet, before the worker has
   started; its thread's stat file and the reading there at its start; or,
   when that file cannot be read (there is no /proc/thread-self outside
   Linux), the lesser of the wall time and the process's CPU time since
   the call started. *)
datatype source = Starting | ThreadClock of string * int | ProcessClock

(* the thread clock's resolution, one tick, in seconds *)
val tick = 0.01

(* A call that is blocked rather than computing uses no CPU, so it is
   still stopped after backstop_factor * t seconds of wall time. *)
val backstop_factor = 20.0

(* The waiter waits in wall slices of the time still left on the clock,
   so that on an idle machine it ends after about t seconds, as timeout
   does.  The worker reads its own clock when f returns, since its stat
   file goes when it exits; the waiter reads it only while the worker
   has not finished, and the worker cannot exit then, since it signals
   with m held.  A reading that fails takes the process clock's
   instead. *)
fun thread_timeout t f x =
  let
    val started = Time.now ()
    val process = Timer.startCPUTimer ()
    val backstop = started + Time.fromReal (backstop_factor * t)
    val source = ref Starting
    val used = ref 0.0
    fun process_seconds () =
      let val {usr, sys} = Timer.checkCPUTimer process in
        Real.min (Time.toReal (Time.now () - started),
                  Time.toReal usr + Time.toReal sys)
      end
    fun seconds () =
      case !source of
          Starting => 0.0
        (* ticks subtracted, then divided, so that a whole number of them
           is the nearest real to its decimal: 50 ticks are 0.5 *)
        | ThreadClock (file, start) => real (stat_ticks file - start) / 100.0
        | ProcessClock => process_seconds ()
    fun timed x =
      let
        val _ = source :=
          (case thread_stat_file () of
               SOME file =>
                 (ThreadClock (file, stat_ticks file)
                  handle IO.Io _ => ProcessClock)
             | NONE => ProcessClock)
        val y = f x
      in
        used := (seconds () handle IO.Io _ => process_seconds ()); y
      end
    fun wait (c, m) finished =
      if finished () then true
      else
        let
          val left = t - (seconds () handle IO.Io _ => process_seconds ())
          val now = Time.now ()
        in
          if left <= 0.0 orelse Time.>= (now, backstop) then false
          else
            (* at least a tick: a shorter slice would end before the
               clock can move, and a blocked worker would have the waiter
               reread its clock without pause until the backstop *)
            let val slice = now + Time.fromReal (Real.max (left, tick)) in
              ignore (ConditionVar.waitUntil
                        (c, m, if Time.< (slice, backstop) then slice
                               else backstop));
              wait (c, m) finished
            end
        end
    val y = timeLimit wait timed x
  in
    (y, !used)
  end

end (* struct *)

(* -------------------------------------------------------------------------
   Tests
   ------------------------------------------------------------------------- *)

(*
load "aiLib"; open aiLib;
load "smlTimeout"; open smlTimeout;

fun f () = 5;
val (_,t1) = add_time (timeout 1.0 f) ();
fun loop () = loop ();
fun g () = (timeout 0.01 loop ()) handle FunctionTimeout => ();
val (_,t2) = add_time g ();
*)
