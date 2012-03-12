open bossLib Theory Parse res_quanTheory Defn Tactic boolLib;
open finite_mapTheory listTheory pairTheory pred_setTheory;
open set_relationTheory sortingTheory stringTheory wordsTheory;
open relationTheory;
open MiniMLTheory terminationProofsTheory;

open pairLib lcsymtacs;

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []
val wf_rel_tac = WF_REL_TAC
val induct_on = Induct_on
val cases_on = Cases_on;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val full_case_tac = BasicProvers.FULL_CASE_TAC;

val _ = new_theory "untypedSafety";

(* Prove that the small step semantics never gets stuck if there is still work
 * to do (i.e., it must detect all type errors).  Thus, it either diverges or
 * gives a result, and it can't do both. *)

val untyped_safety_exp_step = Q.prove (
`∀envC env e c.
  (e_step (envC, env, e, c) = Estuck) = 
  (c = []) ∧ ((?v. e = Val v) ∨ (?err. e = Raise err))`,
rw [e_step_def, continue_def, push_def, return_def] >>
every_case_tac);

val e_step_cenv_same = Q.store_thm("e_step_cenv_same",
`!envC env e c envC' env' e' c'.
  (e_step (envC, env, e, c) = Estep (envC', env', e', c')) ⇒
  (envC = envC')`,
rw [e_step_def, continue_def, push_def, return_def] >>
every_case_tac >>
fs []);

val e_step_rtc_cenv_same_lem = Q.prove (
`!s s'. e_step_reln^* s s' ⇒
  !envC env e c envC' env' e' c'.
  (s = (envC, env, e, c)) ∧
  (s' = (envC', env', e', c')) ⇒
  (envC = envC')`,
HO_MATCH_MP_TAC RTC_INDUCT >>
rw [] >>
PairCases_on `s'` >>
fs [e_step_reln_def] >>
metis_tac [e_step_cenv_same]);

val e_step_rtc_cenv_same = Q.store_thm("e_step_rtc_cenv_same",
`!envC env e c envC' env' e' c'. 
  e_step_reln^* (envC, env, e, c) (envC', env', e', c') 
  ⇒
  (envC = envC')`,
metis_tac [e_step_rtc_cenv_same_lem]);

val small_exp_safety1 = Q.prove (
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

val small_exp_safety2 = Q.prove (
`!cenv env e.
  e_diverges cenv env e ∨ ?r. small_eval cenv env e [] r`,
rw [e_diverges_def, METIS_PROVE [] ``x ∨ y = ~x ⇒ y``, e_step_reln_def] >>
cases_on `e_step (cenv',env',e',c')` >>
fs [untyped_safety_exp_step] >>
`cenv = cenv'` by metis_tac [e_step_rtc_cenv_same] >|
[PairCases_on `p` >> 
     fs [],
 qexists_tac `Rerr Rtype_error` >>
     rw [small_eval_def] >>
     metis_tac [],
 qexists_tac `Rval v` >>
     rw [small_eval_def] >>
     metis_tac [],
 qexists_tac `Rerr (Rraise err)` >>
     rw [small_eval_def] >>
     metis_tac []]);

val untyped_safety_exp = Q.store_thm ("untyped_safety_exp",
`!cenv env e. (?r. small_eval cenv env e [] r) = ¬e_diverges cenv env e`,
metis_tac [small_exp_safety2, small_exp_safety1]);

val untyped_safety_step = Q.prove (
`∀envC env ds st.
  (d_step (envC, env, ds, st) = Dstuck) = (ds = []) ∧ (st = NONE)`,
rw [d_step_def, e_step_def, continue_def, push_def, return_def] >>
every_case_tac);

val untyped_safety_thm = Q.prove (
`!cenv env ds.
  diverges cenv env ds ∨ ?r. d_small_eval cenv env ds NONE r`,
rw [diverges_def, METIS_PROVE [] ``x ∨ y = ~x ⇒ y``, d_step_reln_def] >>
cases_on `d_step (cenv',env',ds',c')` >>
fs [untyped_safety_step] >|
[PairCases_on `p` >> fs [],
 qexists_tac `Rerr (Rraise e)` >>
     rw [d_small_eval_def] >>
     metis_tac [],
 qexists_tac `Rerr Rtype_error` >>
     rw [d_small_eval_def] >>
     metis_tac [],
 qexists_tac `Rval env'` >>
     rw [d_small_eval_def] >>
     metis_tac []]);

val untyped_safety_thm2 = Q.prove (
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

val untyped_safety = Q.store_thm ("untyped_safety",
`!cenv env ds. (?r. d_small_eval cenv env ds NONE r) = ~diverges cenv env ds`,
metis_tac [untyped_safety_thm2, untyped_safety_thm]);

val _ = export_theory ();
