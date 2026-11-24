structure Refute_ThreadClock :> Refute_ThreadClock =
struct

(* Linux reports a thread's CPU time in /proc/<pid>/task/<tid>/stat,
   fields 14 and 15 (utime and stime), in ticks of USER_HZ, which is 100
   on most ports (Alpha's is 1024); a thread finds its own file through
   the /proc/thread-self link.  A thread cannot use more CPU time than the
   wall time that passes, so a reading ahead of the wall clock shows
   another tick rate, and the clock then takes the process's.  The
   process's CPU time is no measure of one thread's: garbage collection
   and other threads compute beside it. *)
fun stat_file () =
  SOME ("/proc/" ^ OS.FileSys.readLink "/proc/thread-self" ^ "/stat")
  handle OS.SysErr _ => NONE

fun unreadable file cause =
  raise IO.Io {name = file, function = "stat_ticks", cause = cause}

(* A thread may read its own stat file while a timeout may interrupt it:
   interrupts are deferred while the file is open, so that the interrupt
   cannot leave it open. *)
fun read_closed file =
  let
    val saved = Thread.getAttributes ()
    val _ = Thread.setAttributes
              [Thread.InterruptState Thread.InterruptDefer]
    fun read () =
      let
        val stream = TextIO.openIn file
        val text = TextIO.inputAll stream
          handle e => (TextIO.closeIn stream; raise e)
      in
        TextIO.closeIn stream; text
      end
    val result = Exn.capture read ()
  in
    Thread.setAttributes saved; Exn.release result
  end

(* the thread's CPU time, utime + stime, in clock ticks *)
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
  (* A record that can't be parsed, or a read that fails with a system
     error, is an unreadable file, and the clock takes the process's. *)
  handle e as OS.SysErr _ => unreadable file e
       | e as Subscript => unreadable file e
       | e as Option => unreadable file e

val tick = 0.01

datatype source = Stat of string * int | Process

type clock = {started : Time.time, process : Timer.cpu_timer,
              source : source ref}

(* The wall clock starts before the first reading of the ticks and is read
   after each later one, so that it spans at least the time they do: a
   reading at 100 ticks a second is then never more than a tick ahead. *)
fun start_reading file =
  let
    val started = Time.now ()
    val process = Timer.startCPUTimer ()
    val source =
      case file of
          SOME name => (Stat (name, stat_ticks name) handle IO.Io _ => Process)
        | NONE => Process
  in
    {started = started, process = process, source = ref source}
  end

fun start () = start_reading (stat_file ())

fun seconds ({started, process, source} : clock) =
  let
    fun wall () = Time.toReal (Time.- (Time.now (), started))
    fun process_seconds () =
      let val {usr, sys} = Timer.checkCPUTimer process in
        Real.min (Time.toReal usr + Time.toReal sys, wall ())
      end
  in
    case !source of
        (* ticks subtracted, then divided, so that a whole number of them
           is the nearest real to its decimal: 50 ticks are 0.5 *)
        Stat (file, ticks) =>
          (let val reading = real (stat_ticks file - ticks) / 100.0 in
             if reading > wall () + tick
             then (source := Process; process_seconds ())
             else reading
           end
           (* a read that fails takes the process clock for this reading
              only *)
           handle IO.Io _ => process_seconds ())
      | Process => process_seconds ()
  end

end
