(* Holmake's work loop waits on its children's pipes with a 100ms poll.
   A round in which poll reports nothing readable is supposed to have
   cost 100ms of sleeping, but poll does not always wait: a descriptor
   whose only pending event is a hang-up or an error is ready at once,
   and Poly/ML's OS.IO.poll reports only the in/out/pri bits, so the
   descriptor arrives as an empty result from a call that did not
   block.  A channel already at EOF behaves the same way, staying in
   the poll set and ready forever.  Unless the loop notices that the
   round achieved nothing, it then spins, and Holmake's own CPU time
   tracks the job's wall-clock time.  Under a CPU rlimit -- as in
   tools/Holmake/tests/gh1353 -- that gets Holmake killed.

   spinner/ holds a rule whose recipe closes both its output streams
   and then stays alive for a few seconds.  The build has to take that
   long (the positive control: without it the measurement below would
   be vacuous) while costing Holmake almost no CPU of its own. *)

open testutils

val op++ = OS.Path.concat
val Holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"
val testdir = OS.FileSys.getDir()
val spindir = testdir ++ "spinner"

fun run_in dir args =
    let val saved = OS.FileSys.getDir()
        val _ = OS.FileSys.chDir dir
        val r = Systeml.systeml (Holmake :: args)
    in
      OS.FileSys.chDir saved; r
    end

(* CPU burned by children of this process, which is what running
   Holmake adds to. *)
fun child_cpu () =
    let val {cutime, cstime, ...} = Posix.ProcEnv.times()
    in Time.+(cutime, cstime) end

fun cleanup () =
    OS.FileSys.remove (spindir ++ "done.txt") handle OS.SysErr _ => ()

val _ = cleanup()

val _ = tprint "work loop idles rather than spins on a hung-up pipe"

val cpu0 = child_cpu()
val wall0 = Time.now()
val result = run_in spindir []
val wall = Time.-(Time.now(), wall0)
val cpu = Time.-(child_cpu(), cpu0)

val _ = cleanup()

val secs = Time.toReal
val _ =
    if not (OS.Process.isSuccess result) then die "FAILED: build failed"
    else if secs wall < 2.0 then
      die ("FAILED: build took only " ^ Real.toString (secs wall) ^
           "s, so the sleeping recipe cannot have run, and the CPU\
           \ measurement means nothing")
    else if secs cpu > 1.0 then
      die ("FAILED: " ^ Real.toString (secs cpu) ^ "s of CPU over " ^
           Real.toString (secs wall) ^ "s of waiting: the work loop is\
           \ busy-waiting")
    else OK()
