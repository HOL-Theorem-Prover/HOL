open HolKernel Parse;

val _ = Portable.catch_SIGINT()

fun cooper0() =
    (test_cases.perform_tests Cooper.COOPER_CONV Cooper.COOPER_TAC ;
     test_cases.perform_cooper_tests Cooper.COOPER_CONV)

fun cooper() = (print "\n\nCooper Test regression tests\n"; cooper0())

fun omega() =
    (test_cases.perform_tests Omega.OMEGA_CONV Omega.OMEGA_TAC;
     test_cases.perform_omega_tests Omega.OMEGA_CONV)

val omega_result = (print "Omega Test regression tests\n"; omega())

fun usage() =
    (TextIO.output(TextIO.stdErr,
                   "Testing Cooper's: bogus commandline: " ^
                   String.concatWith " " (CommandLine.arguments()) ^ "\n");
     TextIO.flushOut TextIO.stdErr)

(* maybe run cooper *)
val _ =
    case OS.Process.getEnv "HOLSELFTESTLEVEL" of
        NONE => if Systeml.ML_SYSNAME = "poly" then cooper() else ()
      | SOME s => (case Int.fromString s of
                       NONE => ()
                     | SOME i => if i >= 2 then cooper() else ())

val _ = print "Testing simplifier integration\n"

open testutils simpLib boolSimps

val _ = tprint "F ==> F equivalent shouldn't loop"
val _ = require (check_result (K true))
                (SIMP_CONV (bool_ss ++ intSimps.OMEGA_ss) [])
                ``x > 2n /\ F ==> x > 1``

val _ = Process.exit (if cooper_result andalso omega_result then
                        Process.success
                      else Process.failure)
