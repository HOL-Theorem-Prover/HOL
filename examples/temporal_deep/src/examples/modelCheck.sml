open HolKernel boolLib bossLib Parse;

open full_ltlTheory arithmeticTheory automaton_formulaTheory xprop_logicTheory prop_logicTheory
     infinite_pathTheory tuerk_tacticsLib symbolic_semi_automatonTheory listTheory pred_setTheory
     temporal_deep_mixedTheory pred_setTheory rich_listTheory set_lemmataTheory pairTheory rltlTheory
     ltl_to_automaton_formulaTheory numLib listLib translationsLib rltl_to_ltlTheory psl_to_rltlTheory
     UnclockedSemanticsTheory SyntacticSugarTheory congLib temporal_deep_simplificationsLib;

open modelCheckLib; (* thus this test is Moscow ML only *)

open testutils;

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

(*
(* Translation to problem on kripke structure *)
ltl_contradiction2ks_fair_emptyness true ltl5;
ltl_contradiction2ks_fair_emptyness___num 1 true ltl5;
ltl_contradiction2ks_fair_emptyness___num 2 true ltl5;
ltl_contradiction2ks_fair_emptyness___num 0 true ltl5;

(* real model checking using smv *)
model_check___ltl_contradiction ltl5;

(* finds as counterexample the path where a always holds *)
model_check___ltl_contradiction ltl6;

(* internally ltl_contradiction2ks_fair_emptyness true is used *)
ltl_contradiction2ks_fair_emptyness true ltl6;

(* some more ltl examples *)
model_check___ltl_equivalent ltl1 ltl2;
model_check___ltl_equivalent_initial ltl1 ltl2;
(* internally this becomes *)
model_check___ltl_contradiction ltl3;

model_check___ltl_equivalent ltl1 ltl2;
(* internally this becomes *)
model_check___ltl_contradiction ltl4;

(* also model checking with concrete kripke structures is possible *)
val M1 = ``symbolic_kripke_structure P_FALSE XP_FALSE``;
val M2 = ``symbolic_kripke_structure (P_NOT (P_PROP a)) (XP_NEXT_PROP a)``;
val M3 = ``symbolic_kripke_structure (P_PROP a) (XP_IMPL(XP_PROP a, XP_NEXT_PROP a))``;

(* no path, so even a contradiction holds *)
ltl_ks_sem2ks_fair_emptyness true ltl5 M1;
ltl_ks_sem2ks_fair_emptyness___num 0 true ltl5 M1;
model_check___ltl_ks_sem ltl5 M1;

(* with some other kripke structure it does not hold any more *)
model_check___ltl_ks_sem ltl5 M2

(* even with a other kripke_structure, a counterexample for ltl6 is
   found, but there are kripke structures that fulfil ltl6 *)
model_check___ltl_ks_sem ltl6 M2
model_check___ltl_ks_sem ltl6 M3

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

psl_ks_sem2ks_fair_emptyness true psl1 pslM1;
psl_ks_sem2ks_fair_emptyness___num 1 true psl1 pslM1;

model_check___psl_ks_sem psl1 pslM1;
model_check___psl_ks_sem psl1 pslM2;

psl_contradiction2ks_fair_emptyness true pslTerm;
psl_contradiction2ks_fair_emptyness___num 0 true pslTerm;

val res = model_check___psl_contradiction psl2;
val eval_res =
    REWRITE_RULE [psl_lemmataTheory.UF_IS_CONTRADICTION___INFINITE_TOP_BOTTOM_FREE_def] (valOf res)

(* example of invalid input formula *)
model_check___psl_contradiction psl3
*)

val _ = Process.exit Process.success;
