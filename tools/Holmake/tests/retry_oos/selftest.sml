open testutils

(* --retry-oos=<n>: a job that fails with Poly/ML's out-of-store message
   on stderr is handed back to the scheduler for up to n further
   attempts.  Each subdirectory has one phony target whose recipe is
   ../oos.sh, which counts its invocations in .oos.count, so the tests
   can check not just the build's verdict but how many attempts it
   took.  All runs use -j2 because the retry lives in the parallel
   builder: it needs the per-job log that only that builder writes. *)

val op++ = OS.Path.concat
val Holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"

val testdir = OS.FileSys.getDir()
val countfile = ".oos.count"

fun reset d = OS.FileSys.remove (d ++ countfile) handle OS.SysErr _ => ()

fun attempts d =
    let
      val strm = TextIO.openIn (d ++ countfile)
      val s = TextIO.inputAll strm
      val _ = TextIO.closeIn strm
    in
      case Int.fromString s of SOME i => i | NONE => ~1
    end handle IO.Io _ => 0

(* Failing runs are expected here, and a failing Holmake prints its
   report; keep that out of the selftest's own output. *)
fun run_in dir args =
    let
      val tmp = OS.FileSys.tmpName()
      val cmd = String.concat
                  ["(cd ", dir, " && ", Holmake, " ",
                   String.concatWith " " args, ") > ", tmp, " 2>&1"]
      val r = Systeml.system_ps cmd
      val strm = TextIO.openIn tmp
      val output = TextIO.inputAll strm
      val _ = TextIO.closeIn strm
      val _ = OS.FileSys.remove tmp handle OS.SysErr _ => ()
    in
      (r, output)
    end

fun check nm {dir, args, succeeds, tries, wants} =
    let
      val d = testdir ++ dir
      val _ = tprint nm
      val _ = reset d
      val (result, output) = run_in d args
      val n = attempts d
      val _ = reset d
      val ok = OS.Process.isSuccess result = succeeds andalso n = tries andalso
               List.all (fn s => String.isSubstring s output) wants
    in
      if ok then OK()
      else die ("FAILED: success=" ^
                Bool.toString (OS.Process.isSuccess result) ^
                " (wanted " ^ Bool.toString succeeds ^ "), attempts=" ^
                Int.toString n ^ " (wanted " ^ Int.toString tries ^
                ")\n--- output ---\n" ^ output ^ "---")
    end

val _ = check "transient out-of-store failure is retried"
              {dir = "transient", args = ["-j2", "--retry-oos=2"],
               succeeds = true, tries = 3,
               wants = ["re-run after Poly/ML"]}

val _ = check "no retry without the option"
              {dir = "transient", args = ["-j2"],
               succeeds = false, tries = 1, wants = []}

val _ = check "--retry-oos=0 is the same as not asking"
              {dir = "transient", args = ["-j2", "--retry-oos=0"],
               succeeds = false, tries = 1, wants = []}

val _ = check "retries are bounded by the count given"
              {dir = "persistent", args = ["-j2", "--retry-oos=2"],
               succeeds = false, tries = 3, wants = []}

val _ = check "a failure without the message is not retried"
              {dir = "otherfail", args = ["-j2", "--retry-oos=2"],
               succeeds = false, tries = 1, wants = []}
