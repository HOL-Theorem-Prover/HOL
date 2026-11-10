(* Holmake's work loop waits on its children's pipes with a 100ms
   poll, and a round that hears nothing is supposed to have spent that
   100ms waiting.  It need not have.  A descriptor belonging to a
   child that has closed its end is ready the moment it is asked
   about, for as long as the job lives -- Linux reports the hang-up as
   POLLHUP, which Poly/ML's OS.IO.poll discards, so poll returns at
   once with an empty result; macOS reports POLLIN too, so the channel
   comes back readable and yields "" forever.  Either way the loop can
   come round again having achieved nothing and waited no time, and
   will busy-wait unless it notices.  Under a CPU rlimit, as in
   tools/Holmake/tests/gh1353, that gets Holmake killed.

   Measuring this needs pairs of builds, never a single absolute
   figure: what a build costs also counts Holmake's startup and
   whatever else the machine is doing, which on a slow or loaded one
   can exceed any threshold worth setting with nothing having spun.
   Only the difference between a build that provokes the condition
   and one that does not is evidence.

   Two pairs, because two different things protect the loop:

     spinner/ vs quiet/   one job, which hangs up its pipes or does
                          not.  The loop has nothing else to attend
                          to, so its idleness is plain.

     both/ vs talky/      a hung-up job beside a chatty one.  This is
                          the shape of a real build, and the one a
                          per-round view of idleness gets wrong: the
                          chatty job keeps every round looking
                          productive while the hung-up one spins the
                          loop in between. *)

open testutils

val op++ = OS.Path.concat
val Holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"
val testdir = OS.FileSys.getDir()

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

val products = ["hung", "talky"]

(* Returns (cpu, wall), or NONE if the build failed. *)
fun measure (dir, args) =
    let
      val d = testdir ++ dir
      fun cleanup () =
          List.app (fn f => OS.FileSys.remove (d ++ f)
                            handle OS.SysErr _ => ())
                   products
      val _ = cleanup()
      val cpu0 = child_cpu()
      val wall0 = Time.now()
      val result = run_in d args
      val wall = Time.-(Time.now(), wall0)
      val cpu = Time.-(child_cpu(), cpu0)
      val _ = cleanup()
    in
      if OS.Process.isSuccess result then SOME (cpu, wall) else NONE
    end

val secs = Time.toReal
fun fmt t = Real.fmt (StringCvt.FIX (SOME 2)) (secs t) ^ "s"

(* Both recipes take about two seconds, so a spin costs about that
   much CPU.  Three quarters of a second of excess is clear of the
   noise between two builds and well under what a spin would show. *)
val allowed = 0.75

fun compare what (provoking, control) =
    let
      val _ = tprint ("work loop idles rather than spins: " ^ what)
    in
      case (measure control, measure provoking) of
          (NONE, _) => die ("FAILED: the " ^ #1 control ^ "/ control\
                            \ build failed")
        | (_, NONE) => die ("FAILED: the " ^ #1 provoking ^ "/ build\
                            \ failed")
        | (SOME (ccpu, cwall), SOME (pcpu, pwall)) =>
          let
            val report =
                #1 provoking ^ "/ " ^ fmt pcpu ^ " CPU over " ^
                fmt pwall ^ ", " ^ #1 control ^ "/ " ^ fmt ccpu ^
                " CPU over " ^ fmt cwall
            (* The positive control: every recipe here sleeps for two
               seconds, so a build that came back sooner did not run
               it, and neither measurement means anything. *)
            val ran = secs cwall >= 1.5 andalso secs pwall >= 1.5
            val excess = Time.-(pcpu, ccpu)
          in
            if not ran then
              die ("FAILED: a build finished too quickly for its recipe\
                   \ to have run; " ^ report)
            else if secs excess > allowed then
              die ("FAILED: hanging up the pipes cost an extra " ^
                   fmt excess ^ " of CPU: the work loop is\
                   \ busy-waiting (" ^ report ^ ")")
            else OK()
          end
    end

val _ = compare "one job" (("spinner", []), ("quiet", []))
val _ = compare "beside a chatty job"
                (("both", ["-j2"]), ("talky", ["-j2"]))
