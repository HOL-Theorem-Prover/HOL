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

   What this measures is how many times the loop went round, which
   Holmake reports under its `multibuild' diagnostic.  Earlier
   versions of this test compared the CPU of a provoking build against
   a control, and that was a mistake: what a build costs in seconds
   depends on the machine and on what else it is doing, and on a busy
   one the difference between two runs of the *same* build was as
   large as the difference the test was looking for.  It failed
   repeatedly on builds that were behaving perfectly.  A count of
   rounds does not move with any of that.  Measured here, a spin runs
   to about a million rounds against a few hundred when the loop is
   idling properly -- three orders of magnitude, with nothing to tune.

   spinner/ is one job that closes its pipes and stays alive, the
   plain form of the problem.  both/ puts that job beside a chatty one
   and is the case a per-round view of idleness gets wrong: the chatty
   job keeps every round looking productive while the hung-up one
   spins the loop in between. *)

open testutils

val op++ = OS.Path.concat
val Holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"
val testdir = OS.FileSys.getDir()

(* A healthy build of either shape runs to a few hundred rounds; a
   spinning one to roughly a million.  Anywhere in between would do. *)
val max_rounds = 5000

(* The recipes sleep for two seconds.  A build that comes back sooner
   did not run one, and then there is nothing to count. *)
val min_wall = 1.5

fun output_of dir args =
    let
      val tmp = OS.FileSys.tmpName()
      val cmd = String.concat
                  ["(cd ", testdir ++ dir, " && ", Holmake,
                   " ", args, " --dbg=multibuild) > ", tmp, " 2>&1"]
      val res = Systeml.system_ps cmd
      val strm = TextIO.openIn tmp
      val content = TextIO.inputAll strm
      val _ = TextIO.closeIn strm
      val _ = OS.FileSys.remove tmp handle OS.SysErr _ => ()
    in
      (res, content)
    end

(* Holmake prints "work loop rounds: n" once per build it drives. *)
val marker = "work loop rounds: "
fun rounds_in s =
    let
      fun digits i =
          let
            val j = ref i
            fun more () = !j < size s andalso
                          Char.isDigit (String.sub(s, !j))
          in
            while more () do j := !j + 1;
            Int.fromString (String.substring(s, i, !j - i))
          end
      fun search i =
          if i + size marker > size s then NONE
          else if String.isPrefix marker (String.extract(s, i, NONE)) then
            digits (i + size marker)
          else search (i + 1)
    in
      search 0
    end

val products = ["hung", "talky"]

fun check what (dir, args) =
    let
      val _ = tprint ("work loop idles rather than spins: " ^ what)
      val d = testdir ++ dir
      fun cleanup () =
          List.app (fn f => OS.FileSys.remove (d ++ f)
                            handle OS.SysErr _ => ())
                   products
      val _ = cleanup()
      val wall0 = Time.now()
      val (res, out) = output_of dir args
      val wall = Time.toReal (Time.-(Time.now(), wall0))
      val _ = cleanup()
    in
      if not (OS.Process.isSuccess res) then
        die ("FAILED: the " ^ dir ^ "/ build failed\n" ^ out)
      else if wall < min_wall then
        die ("FAILED: " ^ dir ^ "/ finished in " ^
             Real.fmt (StringCvt.FIX (SOME 2)) wall ^
             "s, too quickly for its recipe to have run")
      else
        case rounds_in out of
            NONE =>
            die ("FAILED: Holmake reported no round count; the test\
                 \ cannot pass without one.  Has the `multibuild'\
                 \ diagnostic moved?\n" ^ out)
          | SOME n =>
            if n > max_rounds then
              die ("FAILED: the work loop went round " ^ Int.toString n ^
                   " times, against " ^ Int.toString max_rounds ^
                   " allowed: it is busy-waiting")
            else OK()
    end

val _ = check "one job" ("spinner", "")
val _ = check "beside a chatty job" ("both", "-j2")
