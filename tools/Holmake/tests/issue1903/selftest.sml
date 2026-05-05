(* Test for github issue 1903: parallel-build error reporting.

   When a parallel build is aborted by a job failure, the output should:
     1. Use a low-key "killed" notice for collateral kills (not the loud
        red "MKILLED" the issue complains about).
     2. End with a "*** Holmake aborted - N target(s) failed" summary
        whose closing lines point at the actual failure, so users do not
        have to scroll past collateral notices to find the real error. *)

open testutils

val op++ = OS.Path.concat
val Holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"
val testdir = OS.FileSys.getDir() ++ "testdir"

fun read_file f =
    let val s = TextIO.openIn f
    in TextIO.inputAll s before TextIO.closeIn s end

fun run_holmake_in dir args =
    let
      val saved = OS.FileSys.getDir()
      val _ = OS.FileSys.chDir dir
      val cmd = String.concatWith " "
                  (Holmake :: args @ [">", "output", "2>&1"])
      val res = OS.Process.system cmd
    in
      OS.FileSys.chDir saved;
      (res, read_file (dir ++ "output"))
    end

fun has s out = String.isSubstring s out
fun missing s out = not (String.isSubstring s out)

fun show_output_on_failure out =
    (print "\n--- captured Holmake output ---\n";
     print out;
     print "--- end captured output ---\n")

fun clean_testdir () =
    OS.Process.system
      ("cd " ^ testdir ^ " && " ^ Holmake ^ " cleanAll > /dev/null 2>&1")

fun expect_failure (label, args, checks) =
    let
      val _ = tprint label
      val _ = ignore (clean_testdir ())
      val (res, output) = run_holmake_in testdir args
      fun fail msg =
          (show_output_on_failure output; die ("FAILED: " ^ msg))
    in
      if OS.Process.isSuccess res then
        fail "sub-Holmake unexpectedly succeeded"
      else
        case List.find (fn (_, p) => not (p output)) checks of
            SOME (msg, _) => fail msg
          | NONE => OK()
    end

(* Default mode: first failure aborts the build.  The slow theories are
   killed mid-flight; only one FAIL is reported. *)
val _ = expect_failure (
  "Default mode: collateral 'killed' (not MKILLED) and final summary",
  ["-j", "4"],
  [("output should NOT contain 'MKILLED'", missing "MKILLED"),
   ("output should contain 'killed' for collateral",  has "killed"),
   ("output should contain a final '*** Holmake aborted'",
    has "*** Holmake aborted"),
   ("output should contain '*** badboyTheory'", has "*** badboyTheory"),
   ("output should contain final 'Full log:' line", has "Full log:"),
   ("output should mention the deliberate failure",
    has "deliberate failure for issue 1903 test")])

(* keep-going mode: every failing job reports its full block inline AND
   in the closing summary; non-failing jobs still complete OK, so no job
   gets killed and "killed" should not appear in the output. *)
val _ = expect_failure (
  "Keep-going mode: failures appear inline AND in final summary",
  ["-k", "-j", "4"],
  [("output should NOT contain 'MKILLED'", missing "MKILLED"),
   ("output should NOT contain 'killed' (slow jobs all finish)",
    missing "killed"),
   ("output should contain a final '*** Holmake aborted'",
    has "*** Holmake aborted"),
   ("output should contain '*** badboyTheory'", has "*** badboyTheory"),
   ("output should mention the deliberate failure",
    has "deliberate failure for issue 1903 test")])

val _ = ignore (clean_testdir ())
