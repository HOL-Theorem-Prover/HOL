(* Regression test: bin/Holmake accepts a -C / --directory flag and
   chdir's to the specified directory before doing any further work.
   Originally exercised by being run as a kernel-sequence directory
   whose Holmakefile set CLINE_OPTIONS = -C subdir -n -- bin/build's
   per-dir Holmake invocation then either honoured the flag or
   crashed.  That implicit shape didn't survive the move to
   parallel_tests (CLINE_OPTIONS only apply when bin/Holmake is
   invoked in this dir, which doesn't happen under -r), so the test
   now spawns Holmake explicitly. *)

open testutils

infix ++
val op++ = OS.Path.concat

val hm = Globals.HOLDIR ++ "bin" ++ "Holmake"
val poly_opts = if Systeml.ML_SYSNAME = "poly" then ["--poly_not_hol"]
                else []

val _ = tprint "Holmake -C subdir -n"
val args = [hm, "-C", "subdir", "-n", "--no-cache", "--no_overlay"] @ poly_opts
val res = Systeml.systeml_out {outfile = "dashC_works-output"} args
val _ = if OS.Process.isSuccess res then OK()
        else die "Holmake -C subdir -n exited non-zero"
