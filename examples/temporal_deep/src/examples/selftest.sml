open HolKernel Parse boolLib bossLib;

open full_ltlTheory automaton_formulaTheory xprop_logicTheory prop_logicTheory
     symbolic_semi_automatonTheory
     temporal_deep_mixedTheory rltlTheory
     ltl_to_automaton_formulaTheory translationsLib rltl_to_ltlTheory psl_to_rltlTheory
     temporal_deep_simplificationsLib;

open testutils;

(* This will run all tests in ltl2omega.sml *)
open ltl2omega;

(* The rest of tests are from modelCheck.sml without using modelCheckLib *)
val ltl1 = ``LTL_SUNTIL (LTL_PROP (P_PROP a), LTL_PROP (P_PROP b))``;
val ltl2 = ``LTL_EVENTUAL (LTL_AND(LTL_PROP (P_PROP b),
                                   LTL_PNEXT(LTL_PALWAYS (LTL_PROP (P_PROP a)))))``;

(* LTL_EQUIVALENT_INITIAL ltl1 ltl2 = LTL_IS_CONTRADICTION ltl3 *)
val ltl3 = liteLib.mk_icomb(``LTL_NOT``,
                            liteLib.mk_icomb(``LTL_EQUIV``, pairLib.mk_pair (ltl1, ltl2)));

(* LTL_EQUIVALENT ltl1 ltl2 = LTL_IS_CONTRADICTION ltl4 *)
val ltl4 = liteLib.mk_icomb(``LTL_EVENTUAL``, ltl3);

val ltl5 = ``LTL_AND(LTL_NEXT(LTL_NEXT (LTL_PROP (P_PROP a))),
                     LTL_ALWAYS (LTL_NOT (LTL_PROP (P_PROP a))))``;

val ltl6 = ``LTL_AND(LTL_NEXT(LTL_NEXT (LTL_PROP (P_PROP a))),
                     LTL_ALWAYS (LTL_PROP (P_PROP a)))``;

val ltl7 = ``LTL_ALWAYS (LTL_PROP (P_PROP a))``;

val test_cases_simple1 =
   [(ltl_contradiction2ks_fair_emptyness___num 1 true, ltl5),
    (ltl_contradiction2ks_fair_emptyness___num 2 true, ltl5),
    (ltl_contradiction2ks_fair_emptyness___num 0 true, ltl5)];

val _ = List.app (ignore o ltl2omega_test_simple) test_cases_simple1;

(* Translation to problem on kripke structure *)
val test_cases_simple2 =
   [(ltl_contradiction2ks_fair_emptyness true, ltl5),
    (ltl_contradiction2ks_fair_emptyness true, ltl6)];

val _ = List.app (ignore o ltl2omega_test_simple) test_cases_simple2;

(* also model checking with concrete kripke structures is possible *)
val M1 = ``symbolic_kripke_structure P_FALSE XP_FALSE``;
val M2 = ``symbolic_kripke_structure (P_NOT (P_PROP a)) (XP_NEXT_PROP a)``;
val M3 = ``symbolic_kripke_structure (P_PROP a) (XP_IMPL(XP_PROP a, XP_NEXT_PROP a))``;

(* no path, so even a contradiction holds *)
val test_cases_simple3 =
   [(ltl_ks_sem2ks_fair_emptyness true ltl2, M1),
    (ltl_ks_sem2ks_fair_emptyness true ltl2, M2),
    (ltl_ks_sem2ks_fair_emptyness true ltl2, M3)];

val _ = List.app (ignore o ltl2omega_test_simple) test_cases_simple3;

val test_cases_simple4 =
   [(ltl_ks_sem2ks_fair_emptyness___num 0 true ltl5, M1),
    (ltl_ks_sem2ks_fair_emptyness___num 0 true ltl5, M2),
    (ltl_ks_sem2ks_fair_emptyness___num 0 true ltl5, M3)];

val _ = List.app (ignore o ltl2omega_test_simple) test_cases_simple4;

(* Similar functions exists also for PSL *)

(* IBM example *)
val psl1 = ``F_ALWAYS (F_IMPLIES(F_STRONG_BOOL (B_PROP aa),
                                 F_WEAK_NEXT_EVENT
                                   (B_PROP bb,
                                    F_WEAK_BEFORE (
                                      F_STRONG_BOOL (B_PROP cc),
                                      F_STRONG_BOOL (B_PROP dd)))))``;

val psl2 = ``F_NOT (F_ALWAYS (F_IMPLIES (F_STRONG_BOOL (B_PROP aa),
                                         F_WEAK_BOOL (B_PROP aa))))``;

(* not clock free *)
val psl3 = ``F_CLOCK (F_ALWAYS (F_IMPLIES (F_STRONG_BOOL (B_PROP aa),
                                           F_WEAK_BOOL (B_PROP aa))),
                      B_TRUE)``;

val pslM1 = ``symbolic_kripke_structure P_TRUE XP_TRUE``;
val pslM2 = ``symbolic_kripke_structure P_TRUE (XP_NOT (XP_PROP aa))``;

val test_cases_simple5 =
   [(psl_ks_sem2ks_fair_emptyness true psl1, pslM1),
    (psl_ks_sem2ks_fair_emptyness true psl1, pslM2),
    (psl_ks_sem2ks_fair_emptyness true psl2, pslM1),
    (psl_ks_sem2ks_fair_emptyness true psl2, pslM2),
(* ERROR (expected): NOT_CLOCK_SERE_FREE
    (psl_ks_sem2ks_fair_emptyness true psl3, pslM1),
    (psl_ks_sem2ks_fair_emptyness true psl3, pslM2),
    (psl_contradiction2ks_fair_emptyness true, psl3),
 *)
    (psl_contradiction2ks_fair_emptyness true, psl1),
    (psl_contradiction2ks_fair_emptyness true, psl2)];

val _ = List.app (ignore o ltl2omega_test_simple) test_cases_simple5;

val _ = Process.exit Process.success;
