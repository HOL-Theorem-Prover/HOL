open bossLib Theory Parse res_quanTheory Defn Tactic boolLib;
open finite_mapTheory listTheory pairTheory pred_setTheory;
open set_relationTheory sortingTheory stringTheory wordsTheory;
open relationTheory;
open MiniMLTheory miniMLProofsTheory bigSmallEquivTheory;

open lcsymtacs;

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []
val wf_rel_tac = WF_REL_TAC
val induct_on = Induct_on
val cases_on = Cases_on;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val full_case_tac = BasicProvers.FULL_CASE_TAC;

val _ = new_theory "determ";

(* ------------------------- Big step determinacy ----------------------- *)

val big_exp_determ = Q.store_thm ("big_exp_determ",
`(∀ cenv env e r1.
   evaluate cenv env e r1 ⇒
   ∀ r2. evaluate cenv env e r2 ⇒
   (r1 = r2)) ∧
 (∀ cenv env es r1.
   evaluate_list cenv env es r1 ⇒
   ∀ r2. evaluate_list cenv env es r2 ⇒
   (r1 = r2)) ∧
 (∀ cenv env v pes r1.
   evaluate_match cenv env v pes r1 ⇒
   ∀ r2. evaluate_match cenv env v pes r2 ⇒
   (r1 = r2))`,
HO_MATCH_MP_TAC evaluate_ind >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_cases]) >>
fs [] >>
rw [] >>
fs [] >>
res_tac >>
fs [] >>
rw []);

val big_exp_determ' = Q.store_thm ("big_exp_determ'",
`(∀ env e r1.
   evaluate' env e r1 ⇒
   ∀ r2. evaluate' env e r2 ⇒
   (r1 = r2)) ∧
 (∀ env es r1.
   evaluate_list' env es r1 ⇒
   ∀ r2. evaluate_list' env es r2 ⇒
   (r1 = r2)) ∧
 (∀ env v pes r1.
   evaluate_match' env v pes r1 ⇒
   ∀ r2. evaluate_match' env v pes r2 ⇒
   (r1 = r2))`,
HO_MATCH_MP_TAC evaluate'_ind >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate'_cases]) >>
fs [] >>
rw [] >>
fs [] >>
res_tac >>
fs [] >>
rw []);

val big_determ = Q.store_thm ("big_determ",
`!cenv env ds r1.
  evaluate_decs cenv env ds r1 ⇒
  !r2.
    evaluate_decs cenv env ds r2
    ⇒
    (r1 = r2)`,
HO_MATCH_MP_TAC evaluate_decs_ind >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_decs_cases]) >>
fs [] >>
rw [] >>
fs [] >>
res_tac >>
fs [] >>
rw [] >>
metis_tac [big_exp_determ, result_11, result_distinct,
           match_result_11, match_result_distinct]);

(* ---------------------- Small step determinacy ------------------------- *)

val small_exp_determ1 = Q.store_thm ("small_exp_determ1",
`!cenv env e r1 r2.
  small_eval cenv env e [] r1 ∧ small_eval cenv env e [] r2
  ⇒
  (r1 = r2)`,
metis_tac [big_exp_determ, small_big_exp_equiv]);

val small_exp_determ2 = Q.store_thm ("small_exp_determ2",
`!cenv env e r.
  ¬(e_diverges cenv env e ∧ ?r. small_eval cenv env e [] r)`,
rw [e_diverges_def, METIS_PROVE [] ``~x ∨ ~y = y ⇒ ~x``] >>
cases_on `r` >>
(TRY (Cases_on `e'`)) >>
fs [small_eval_def, e_step_reln_def] >|
[`∀cenv'' env'' e'' c''.
    e_step (cenv,env',Val a,[]) ≠ Estep (cenv'',env'',e'',c'')`
         by rw [e_step_def, continue_def] >>
     metis_tac [],
 metis_tac [e_step_result_distinct],
 `∀cenv'' env'' e''' c''.
    e_step (cenv,env',Raise e'',[]) ≠ Estep (cenv'',env'',e''',c'')`
         by rw [e_step_def, continue_def] >>
     metis_tac []]);

val small_determ1 = Q.store_thm ("small_determ1",
`!cenv env ds r1 r2.
  d_small_eval cenv env ds NONE r1 ∧ d_small_eval cenv env ds NONE r2
  ⇒
  (r1 = r2)`,
metis_tac [big_determ, small_big_equiv]);

val small_determ2 = Q.store_thm ("small_determ2",
`!cenv env ds r.
  ¬(diverges cenv env ds ∧ ?r. d_small_eval cenv env ds NONE r)`,
rw [diverges_def, METIS_PROVE [] ``~x ∨ ~y = y ⇒ ~x``] >>
cases_on `r` >>
TRY (cases_on `e`) >>
fs [d_small_eval_def, d_step_reln_def] >|
[`∀cenv'' env'' ds'' c''.
    d_step (cenv',a,[],NONE) ≠ Dstep (cenv'',env'',ds'',c'')`
         by rw [d_step_def] >>
     metis_tac [],
 metis_tac [d_step_result_distinct],
 metis_tac [d_step_result_distinct]]);


val _ = export_theory ();

