(* Interrupt regressions for [ParList].  HOL delivers Ctrl-C as
   [Thread.broadcastInterrupt], which a thread whose broadcast flag is clear
   does not even record, so each test plants the broadcast in the window it
   is about through [ParList_Test] rather than racing it. *)

fun die s = (print (s ^ "\n"); OS.Process.exit OS.Process.failure);

fun tprint s = print (StringCvt.padRight #" " 70 s);

fun ok () = print "OK\n";

fun sleep secs = OS.Process.sleep (Time.fromReal secs);

fun wait_until p = if p () then () else (sleep 0.001; wait_until p);

(* Each test runs with the attributes HOL's REPL gives the top level.
   Between tests the top level defers with the broadcast flag clear, so a
   broadcast still in flight cannot land on an unrelated step. *)
val deferred =
  [Thread.EnableBroadcastInterrupt false,
   Thread.InterruptState Thread.InterruptDefer];

val _ = Thread.setAttributes deferred;

fun clear_pending () =
  (Thread.setAttributes [Thread.InterruptState Thread.InterruptSynch];
   (Thread.testInterrupt () handle Interrupt => ());
   Thread.setAttributes deferred);

fun as_repl e =
  Thread_Attributes.with_attributes Thread_Attributes.public_interrupts
    (fn _ => Exn.capture e ());

fun check_interrupt what outcome =
  case outcome of
      Exn.Exn error =>
        if Exn.is_interrupt error then ()
        else die ("Unexpected exception: " ^ General.exnMessage error)
    | Exn.Res _ => die what;

(* A broadcast arriving while [fork_one] holds its mask must survive it.
   Under a mask that clears the broadcast flag nothing records the Ctrl-C
   and the whole map runs to completion. *)
val _ = tprint "Ctrl-C inside the fork window is not lost";

val fork_window =
  let
    val _ = ParList_Test.fork_hook :=
      SOME (fn () => Thread.broadcastInterrupt ())
    val outcome = as_repl (fn () =>
      ParList.map_with_workers 2 (fn n => n) (List.tabulate (8, fn n => n)))
    val _ = ParList_Test.fork_hook := NONE
    val _ = clear_pending ()
  in
    outcome
  end;

val _ = check_interrupt "the fork window dropped the broadcast" fork_window;
val _ = ok ();

(* A job that swallows its interrupt must not go on draining the queue: the
   caller's Ctrl-C closes it, so each worker costs one more job at most.
   Every job blocks until the join is under way, which puts the whole queue
   behind the point where the caller has given up waiting. *)
val _ = tprint "Ctrl-C at the join stops jobs being handed out";

val (join_window, handed_out) =
  let
    val total = 200
    val counter = Mutex.mutex ()
    val started = ref 0
    val go = ref false
    val stop = ref false
    fun bump () =
      (Mutex.lock counter; started := !started + 1; Mutex.unlock counter)
    fun job n =
      (Thread.setAttributes [Thread.InterruptState Thread.InterruptDefer];
       bump ();
       wait_until (fn () => !go);
       n)
    fun ctrl_c () =
      if !stop then ()
      else (Thread.broadcastInterrupt (); sleep 0.005; ctrl_c ())
    val _ = ParList_Test.join_hook := SOME (fn () => go := true)
    val user = Standard_Thread.fork
      {name = "ParList.selftest", stack_limit = NONE, interrupts = false}
      (fn () => (wait_until (fn () => !started >= 2); ctrl_c ()))
    val outcome = as_repl (fn () =>
      ParList.map_with_workers 2 job (List.tabulate (total, fn n => n)))
    val _ = stop := true
    val _ = ParList_Test.join_hook := NONE
    val _ = wait_until (fn () => not (Thread.isActive user))
    val _ = clear_pending ()
  in
    (outcome, !started)
  end;

val _ = check_interrupt "the caller's Ctrl-C was swallowed" join_window;
val _ =
  if handed_out = 2 then ok ()
  else die ("jobs kept being handed out: " ^ Int.toString handed_out ^
            " started, expected 2");

val _ = tprint "map_with_workers keeps input order";
val _ =
  if ParList.map_with_workers 3 (fn n => n * n) (List.tabulate (20, fn n => n))
     = List.tabulate (20, fn n => n * n)
  then ok () else die "wrong results";

val _ = tprint "get_some_with_workers finds an answer";
val _ =
  case ParList.get_some_with_workers 3
         (fn n => if n = 17 then SOME n else NONE)
         (List.tabulate (20, fn n => n)) of
      SOME 17 => ok ()
    | _ => die "wrong answer";

(* Restoration under cancellation.  [Portable.bracket], and the
   [with_flag], [genwith_flag] and [finally] built on it, run their
   restore with interrupts deferred: a restore under way when the
   interrupt arrives finishes, and the interrupt is delivered after it.
   The restores here are slow on purpose, so that the interrupt lands
   inside them. *)

fun slow_flag delay =
  let
    val flag = ref false
    fun set v = if v then flag := true else (sleep delay; flag := false)
  in
    (flag, {get = fn () => !flag, set = set})
  end;

(* [f ()] on a thread that takes one interrupt asynchronously, as
   [Timeout.apply] runs its tactic, and an interrupt [d] seconds in, as
   its timer sends *)
fun timed d f =
  let
    val outcome = ref NONE
    val t = Thread.fork (fn () => outcome := SOME (Exn.capture f ()),
                         [Thread.InterruptState Thread.InterruptAsynchOnce,
                          Thread.EnableBroadcastInterrupt false])
    val _ = sleep d
    (* the thread may be gone already, if [f] was quick *)
    val _ = Thread.interrupt t
            handle e => if Thread.isActive t then raise e else ()
    val _ = wait_until (fn () => not (Thread.isActive t))
  in
    case !outcome of
        SOME r => r
      | NONE => die "the thread died before recording its outcome"
  end;

fun check_timeout what outcome =
  check_interrupt (what ^ ": the interrupt was lost") outcome;

fun check_restored what flags =
  if List.all (fn f => not (!f)) flags then ok ()
  else die (what ^ ": flag not restored");

val _ = tprint "genwith_flag: deadline in the restore after a normal return";
val _ =
  let
    val (flag, acc) = slow_flag 0.05
    val r = timed 0.01 (Portable.genwith_flag (acc, true) (fn () => ()))
  in
    check_timeout "genwith_flag" r; check_restored "genwith_flag" [flag]
  end;

val _ = tprint "finally: deadline in the finisher after a normal return";
val _ =
  let
    val finished = ref false
    val r = timed 0.01 (Portable.finally
                          (fn () => (sleep 0.05; finished := true))
                          (fn () => ()))
  in
    check_timeout "finally" r;
    if !finished then ok () else die "finally: finisher cut short"
  end;

val _ = tprint "genwith_flag: interrupted body, slow restore";
val _ =
  let
    val (flag, acc) = slow_flag 0.05
    val r = timed 0.01 (Portable.genwith_flag (acc, true)
                          (fn () => sleep 2.0))
  in
    check_timeout "interrupted body" r; check_restored "interrupted body" [flag]
  end;

val _ = tprint "nested genwith_flag: deadline in the inner body";
val _ =
  let
    val (f1, a1) = slow_flag 0.03
    val (f2, a2) = slow_flag 0.03
    val r = timed 0.01 (Portable.genwith_flag (a1, true)
                          (Portable.genwith_flag (a2, true)
                             (fn () => sleep 2.0)))
  in
    check_timeout "nested body" r; check_restored "nested body" [f1, f2]
  end;

val _ = tprint "nested genwith_flag: deadline in the inner restore";
val _ =
  let
    val (f1, a1) = slow_flag 0.03
    val (f2, a2) = slow_flag 0.03
    val r = timed 0.01 (Portable.genwith_flag (a1, true)
                          (Portable.genwith_flag (a2, true) (fn () => ())))
  in
    check_timeout "nested restore" r; check_restored "nested restore" [f1, f2]
  end;

val _ = tprint "with_flag: results and exceptions pass through, flag restored";
val _ =
  let
    val r = ref 0
    val v = Portable.with_flag (r, 1) (fn () => !r + 41) ()
    val e = Exn.capture (Portable.with_flag (r, 2)
                           (fn () => raise Fail "x")) ()
  in
    case (v, !r, e) of
        (42, 0, Exn.Exn (Fail "x")) => ok ()
      | _ => die "with_flag changed a result or left the flag set"
  end;

(* Another thread interrupts while the restore runs: the restore
   finishes, and the caller still sees the interrupt. *)
fun caller_interrupt name state =
  let
    val _ = tprint ("caller interrupt during the restore (" ^ name ^ ")")
    val (flag, acc) = slow_flag 0.05
    val restoring = ref false
    val acc' = {get = #get acc,
                set = fn v => (if v then () else restoring := true;
                               #set acc v)}
    val outcome = ref NONE
    fun run () =
      outcome := SOME (Exn.capture
                         (Portable.genwith_flag (acc', true) (fn () => ())) ())
    val t = Thread.fork (run, [Thread.InterruptState state,
                               Thread.EnableBroadcastInterrupt false])
    val _ = wait_until (fn () => !restoring)
    val _ = Thread.interrupt t
    val _ = wait_until (fn () => not (Thread.isActive t))
  in
    case !outcome of
        SOME r => (check_interrupt (name ^ ": interrupt lost") r;
                   check_restored name [flag])
      | NONE => die (name ^ ": restore cut short")
  end;

val _ = caller_interrupt "AsynchOnce" Thread.InterruptAsynchOnce;
val _ = caller_interrupt "Asynch" Thread.InterruptAsynch;

(* The REPL thread is fully asynchronous: masking the restores must not
   make it one-shot inside the body, or a Ctrl-C after a swallowed one
   would no longer stop anything. *)
val _ = tprint "asynch caller: a second interrupt stops a swallowing body";
val _ =
  let
    val r = ref 0
    val swallowed = ref false
    val outcome = ref NONE
    fun spin () = (sleep 0.001; spin ())
    fun body () = ((spin () handle Interrupt => swallowed := true); spin ())
    fun run () =
      outcome := SOME (Exn.capture (Portable.with_flag (r, 1) body) ())
    val t = Thread.fork (run, [Thread.InterruptState Thread.InterruptAsynch,
                               Thread.EnableBroadcastInterrupt false])
    val _ = sleep 0.02
    val _ = Thread.interrupt t
    val _ = wait_until (fn () => !swallowed)
    val _ = sleep 0.02
    val _ = Thread.interrupt t
    val deadline = Time.+ (Time.now (), Time.fromReal 2.0)
    val _ = wait_until (fn () => not (Thread.isActive t) orelse
                                 Time.> (Time.now (), deadline))
  in
    if Thread.isActive t then (Thread.kill t; die "body not stopped")
    else
      case !outcome of
          SOME x => (check_interrupt "second interrupt lost" x;
                     if !r = 0 then ok () else die "flag not restored")
        | NONE => die "no outcome"
  end;

(* A one-shot interrupt the body took is spent: leaving the bracket must
   not re-arm it. *)
val _ = tprint "a one-shot interrupt taken in the body stays spent";
val _ =
  let
    val r = ref 0
    val taken = ref false
    val state = ref NONE
    fun spin () = (sleep 0.001; spin ())
    fun body () = spin () handle Interrupt => taken := true
    fun run () =
      (Portable.with_flag (r, 1) body ();
       state := SOME (Thread_Attributes.convert_attributes
                        (Thread_Attributes.get_attributes ())))
    val t = Thread.fork (run,
                         [Thread.InterruptState Thread.InterruptAsynchOnce,
                          Thread.EnableBroadcastInterrupt false])
    val _ = sleep 0.02
    val _ = Thread.interrupt t
    val _ = wait_until (fn () => not (Thread.isActive t))
    fun synch (Thread.InterruptState Thread.InterruptSynch) = true
      | synch _ = false
  in
    case !state of
        SOME atts => if List.exists synch atts then ok ()
                     else die "one-shot interrupt re-armed"
      | NONE => die "with_flag did not return"
  end;
