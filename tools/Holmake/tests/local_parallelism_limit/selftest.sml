open testutils

val op++ = OS.Path.concat
val Holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"

val testdir = OS.FileSys.getDir()

fun clean_state d =
    let
      val lock = d ++ ".plimit.lock"
      val count = d ++ ".plimit.count"
    in
      OS.FileSys.remove lock handle OS.SysErr _ => ();
      OS.FileSys.remove count handle OS.SysErr _ => ()
    end

fun run_in dir args =
    let val saved = OS.FileSys.getDir()
        val _ = OS.FileSys.chDir dir
        val r = Systeml.systeml (Holmake :: args)
    in
      OS.FileSys.chDir saved; r
    end

fun run_in_capturing_stderr dir args =
    let
      val tmp = OS.FileSys.tmpName()
      val argstr = String.concatWith " " args
      val cmd = String.concat
                  ["(cd ", dir, " && ", Holmake,
                   if argstr = "" then "" else " " ^ argstr,
                   ") 2> ", tmp]
      val r = Systeml.system_ps cmd
      val s = TextIO.openIn tmp
      val content = TextIO.inputAll s
      val _ = TextIO.closeIn s
      val _ = OS.FileSys.remove tmp handle OS.SysErr _ => ()
    in
      (r, content)
    end

(* -----------------------------------------------------------------------
   Test 1: LOCAL_PARALLELISM_LIMIT = 1 enforces total-1 cap.

   Six phony targets each run check.sh 1, which atomically increments
   a shared counter and exits 1 if the counter exceeds 1.  Built with
   -j 4, so without enforcement we'd see counter values up to 4 and
   the build would fail.  Build success == cap was respected.
   ----------------------------------------------------------------------- *)
val _ = tprint "n=1: targets run with total-1 cap"
val capped1 = testdir ++ "capped1"
val _ = clean_state capped1
val result1 = run_in capped1 ["-j", "4"]
val _ = clean_state capped1
val _ = if OS.Process.isSuccess result1 then OK()
        else die "FAILED"

(* -----------------------------------------------------------------------
   Test 2: LOCAL_PARALLELISM_LIMIT = 2 enforces total-2 cap.
   ----------------------------------------------------------------------- *)
val _ = tprint "n=2: targets run with total-2 cap"
val capped2 = testdir ++ "capped2"
val _ = clean_state capped2
val result2 = run_in capped2 ["-j", "4"]
val _ = clean_state capped2
val _ = if OS.Process.isSuccess result2 then OK()
        else die "FAILED"

(* -----------------------------------------------------------------------
   Test 3: invalid value warns and is then ignored (build succeeds).
   ----------------------------------------------------------------------- *)
val _ = tprint "invalid value warns and is ignored"
val bad = testdir ++ "bad"
val (result3, stderr) = run_in_capturing_stderr bad []
val saw_warning = String.isSubstring "LOCAL_PARALLELISM_LIMIT" stderr
val _ = if OS.Process.isSuccess result3 andalso saw_warning then OK()
        else die ("FAILED: success=" ^
                  Bool.toString (OS.Process.isSuccess result3) ^
                  " saw_warning=" ^ Bool.toString saw_warning ^
                  "\n--- stderr ---\n" ^ stderr ^ "---")
