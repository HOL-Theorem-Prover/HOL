open HolKernel Parse;

val _ = Portable.catch_SIGINT()

fun cooper() =
    test_cases.perform_tests Cooper.COOPER_CONV Cooper.COOPER_TAC andalso
    test_cases.perform_cooper_tests Cooper.COOPER_CONV

fun omega() = test_cases.perform_tests Omega.OMEGA_CONV Omega.OMEGA_TAC andalso
              test_cases.perform_omega_tests Omega.OMEGA_CONV

val omega_result = (print "Omega Test regression tests\n"; omega())

fun usage() =
    (TextIO.output(TextIO.stdErr,
                   "Testing Cooper's: bogus commandline: " ^
                   String.concatWith " " (CommandLine.arguments()) ^ "\n");
     TextIO.flushOut TextIO.stdErr)

val cooper_result =
    case CommandLine.arguments() of
      [] => if Systeml.ML_SYSNAME = "poly" then cooper() else (usage(); true)
    | [x] => let
      in
        case Int.fromString x of
          SOME n => if n >= 2 then cooper()
                    else true
        | NONE => (usage(); true)
      end
    | _ => (usage(); true)

val _ = print "Testing simplifier integration\n"

open testutils simpLib boolSimps

val _ = tprint "F ==> F equivalent shouldn't loop"
val th = SIMP_CONV (bool_ss ++ intSimps.OMEGA_ss) [] ``x > 2n /\ F ==> x > 1``
         handle e => die (General.exnMessage e)
val _ = print "OK\n"

val _ = Process.exit (if cooper_result andalso omega_result then
                        Process.success
                      else Process.failure)
