open HolKernel Parse;
open testutils simpLib boolSimps

val erc = ref 0
val _ = diemode := Remember erc
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

val _ = tprint "F ==> F equivalent shouldn't loop"
val _ = require (check_result (K true))
                (SIMP_CONV (bool_ss ++ intSimps.OMEGA_ss) [])
                ``x > 2n /\ F ==> x > 1``

val _ = shouldfail {testfn = intLib.ARITH_CONV, printresult = thm_to_string,
                    printarg = (fn t => "ARITH_CONV “" ^ term_to_string t ^
                                        "” fails correctly (gh1209)"),
                    checkexn = is_struct_HOL_ERR "IntDP_Munge"}
                   “x (0i) + 0 % 5 = 0i”


val _ = convtest ("decide_closed_presburger w/genvar",
                  OmegaShell.decide_closed_presburger,
                  “! $var$(%%genvar%%801) q r.
                      0i = q * 5 + r /\ 0 <= r /\ r < 5 ==>
                      $var$(%%genvar%%801) + r = 0”,
                  boolSyntax.F);

val _ = convtest ("decide_closed_presburger witout genvar",
                  OmegaShell.decide_closed_presburger,
                  “!v q r.
                      0i = q * 5 + r /\ 0 <= r /\ r < 5 ==> v + r = 0”,
                  boolSyntax.F);

val _ = convtest ("OmegaSimple.simple_CONV",
                  OmegaSimple.simple_CONV,
                  “?i q:int. 0 <= 1 * i + -5 * q + -1 /\ 0 <= 1 * q + 0 /\
                             0 <= -1 * q + 0”,
                  boolSyntax.T);

val _ = convtest ("decide_closed_presburger w/genvar % 4",
                  OmegaShell.decide_closed_presburger,
                  “! $var$(%%genvar%%801) q r.
                      0i = q * 4 + r /\ 0 <= r /\ r < 4 ==>
                      $var$(%%genvar%%801) + r = 0”,
                  boolSyntax.F);

val _ = exit_count0 erc
