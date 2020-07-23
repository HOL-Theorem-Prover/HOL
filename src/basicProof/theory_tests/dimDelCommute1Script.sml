open HolKernel Parse boolLib simpLib BasicProvers
open testutils

val _ = new_theory "dimDelCommute1";
(* checks that

    - after srw_ss() is initialised,
    - a temp_delsimps call is not masked/invalidated by a subsequent
      diminish_srw_ss call
 *)

val _ = srw_ss()
val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = diminish_srw_ss ["ABBREV"]

val _ = shouldfail {checkexn = fn Conv.UNCHANGED => true | _ => false,
                    printarg = fn t => "Should UNCHANGE: "^term_to_string t,
                    printresult = thm_to_string,
                    testfn = SIMP_CONV (srw_ss()) []}
                   “ARB = x ==> P x T”

val _ = export_theory();
