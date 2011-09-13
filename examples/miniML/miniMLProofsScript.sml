open bossLib Theory Parse res_quanTheory Defn Tactic boolLib;
open finite_mapTheory listTheory pairTheory pred_setTheory;
open set_relationTheory sortingTheory stringTheory wordsTheory;
open relationTheory;
open MiniMLTheory;

open lcsymtacs;

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []
val wf_rel_tac = WF_REL_TAC
val induct_on = Induct_on
val cases_on = Cases_on;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val full_case_tac = BasicProvers.FULL_CASE_TAC;

val _ = new_theory "miniMLProofs";

(* --------------------- Termination proofs -------------------------------- *)

val (lookup_def, lookup_ind) =
  tprove_no_defn ((lookup_def, lookup_ind), 
  WF_REL_TAC `measure (λ(x,y). LENGTH y)` >>
  rw []);
val _ = save_thm ("lookup_def", lookup_def);
val _ = save_thm ("lookup_ind", lookup_ind);

val (pmatch_def, pmatch_ind) =
  tprove_no_defn ((pmatch_def, pmatch_ind),
  wf_rel_tac 
  `inv_image $< (λx. case x of INL (a,p,b,c) -> pat_size p || INR (a,ps,b,c) ->
  pat1_size ps)`);
val _ = save_thm ("pmatch_def", pmatch_def);
val _ = save_thm ("pmatch_ind", pmatch_ind);

val (find_recfun_def, find_recfun_ind) =
  tprove_no_defn ((find_recfun_def, find_recfun_ind),
  WF_REL_TAC `measure (λ(x,y). LENGTH y)` >>
  rw []);
val _ = save_thm ("find_recfun_def", find_recfun_def);
val _ = save_thm ("find_recfun_ind", find_recfun_ind);

val (type_subst_def, type_subst_ind) =
  tprove_no_defn ((type_subst_def, type_subst_ind),
  WF_REL_TAC `measure (λ(x,y). t_size y)` >>
  rw [] >|
  [induct_on `ts` >>
       rw [t_size_def] >>
       res_tac >>
       decide_tac,
   decide_tac,
   decide_tac]);
val _ = save_thm ("type_subst_def", type_subst_def);
val _ = save_thm ("type_subst_ind", type_subst_ind);

(* ------------------------------------------------------------------------- *)

(* Prove that the small step semantics never gets stuck if there is still work
 * to do (i.e., it must detect all type errors *)

val untyped_safety_thm = Q.store_thm ("untyped_safety_thm",
`∀envC env ds st. 
  (d_step (envC, env, ds, st) = Dstuck) = (ds = []) ∧ (st = NONE)`,
rw [d_step_def, e_step_def, continue_def, push_def, return_def, 
    type_error_def] >>
every_case_tac >>
fs [LET_THM, do_app_def] >>
every_case_tac >>
fs []);

(* ------------------------- Big step determinacy ----------------------- *)

val big_exp_determ = Q.prove (
`(∀ cenv env e bv1.
   evaluate cenv env e bv1 ⇒
   ∀ bv2. evaluate cenv env e bv2 ⇒
   (bv1 = bv2)) ∧
 (∀ cenv env es bv1.
   evaluate_list cenv env es bv1 ⇒
   ∀ bv2. evaluate_list cenv env es bv2 ⇒
   (bv1 = bv2)) ∧
 (∀ cenv env v pes bv1.
   evaluate_match cenv env v pes bv1 ⇒
   ∀ bv2. evaluate_match cenv env v pes bv2 ⇒
   (bv1 = bv2))`,
HO_MATCH_MP_TAC evaluate_ind >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_cases]) >>
fs [] >>
rw [] >>
fs [] >>
res_tac >>
fs [] >>
rw []);
 

(*
val evaluate_ctxts_def = Q.prove (
`∀ cenv v v' c env cs bv err.
  (evaluate_ctxts cenv [] v (Bvalue v') = (v = v')) ∧
  (evaluate_ctxts cenv ((c,env)::cs) v bv =
     (∃ v' err.
       (evaluate_ctxt cenv env c v (Bvalue v') ∧
        evaluate_ctxts cenv cs v' bv) ∨
       (evaluate_ctxt cenv env c v (Berror err) ∧ 
        (bv = Berror err))))`,
rw [] >|
[rw [Once evaluate_ctxts_cases] >>
     metis_tac [],
 EQ_TAC >>
     rw [] >|
     [pop_assum 
            (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_ctxts_cases]) >>
          rw [] >>
          metis_tac [],
      rw [Once evaluate_ctxts_cases] >>
          metis_tac [],
      rw [Once evaluate_ctxts_cases] >>
          metis_tac []]]);

val evaluate_value = Q.prove (
`(∀ v cenv env. 
  evaluate cenv env (Val v) (Bvalue v)) ∧
 (∀ vs cenv env. 
  evaluate_list cenv env (MAP Val vs) (Bvalue vs))`, 
Induct >>
rw [] >>
rw [Once evaluate_cases] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_cases]) >>
metis_tac []);

val evaluate_value_determ = Q.prove (
`!v v' cenv env. 
  evaluate cenv env (Val v) (Bvalue v') ⇒ (v = v')`,
rw [] >>
metis_tac [evaluate_value, big_step_result_distinct, big_step_result_11,
           big_exp_determ]);

val ev_lem1 = Q.prove (
`!cenv env v err. ¬evaluate cenv env (Val v) (Berror err)`,
rw [] >>
CCONTR_TAC >>
`evaluate cenv env (Val v) (Bvalue v)` by metis_tac [evaluate_value] >>
fs [] >>
imp_res_tac big_exp_determ >>
fs []);
*)

(*
val exp_evaluation_preservation = Q.prove (
`!cenv env e c bv cenv' env' e' c'. 
  evaluate_state (cenv,env,e,c) bv ∧ 
  (e_step (cenv,env,e,c) = (State (cenv',env',e',c')))
  ⇒ 
  evaluate_state (cenv',env',e',c') bv`
rw [e_step_def, push_def] >>
cases_on `e` >>
fs [] >>
rw [] >|
[fs [continue_def] >>
     cases_on `c` >>
     fs [] >>
     cases_on `h` >>
     fs [] >>
     cases_on `q` >>
     fs [push_def] >|
     [every_case_tac >>
          fs [evaluate_state_cases, evaluate_ctxts_def] >>
          qpat_assum `evaluate envC env (Val vpat) bvpat`
            (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_cases]) >>
          rw [evaluate_ctxts_def] >>
          fs [evaluate_ctxt_cases] >>
          metis_tac [],
      every_case_tac >>
          fs [evaluate_state_cases, evaluate_ctxts_def,
              evaluate_ctxt_cases] >>
          rw [] >>
          imp_res_tac evaluate_value_determ >>
          metis_tac [big_step_result_distinct, evaluate_value, big_exp_determ],
      every_case_tac >>
          fs [evaluate_state_cases, evaluate_ctxts_def,
              evaluate_ctxt_cases] >>
          rw [] >>
          imp_res_tac evaluate_value_determ >>
          fs [] >>
          metis_tac [big_step_result_distinct, evaluate_value, big_exp_determ],
      every_case_tac >>
          fs [return_def] >>
          rw [] >>
          fs [evaluate_state_cases, evaluate_ctxts_def, evaluate_ctxt_cases] >>
          rw [] >>
          imp_res_tac evaluate_value_determ >>
          fs [ev_lem1] >>
          rw [] >>
          qpat_assum `evaluate cenv env' (Log oppat vpat e) bvpat`
            (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_cases]) >>
          fs [] >>
          imp_res_tac evaluate_value_determ >>
          fs [ev_lem1] >>
          metis_tac [big_step_result_distinct, evaluate_value, big_exp_determ],
      every_case_tac >>
          fs [evaluate_state_cases, evaluate_ctxts_def,
              evaluate_ctxt_cases, ev_lem1] >>
          rw [] >>
          imp_res_tac evaluate_value_determ >>
          fs [] >>
          qpat_assum `evaluate cenv env' (Op oppat vpat e) bvpat`
            (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_cases]) >>
          fs [evaluate_ctxts_def, evaluate_ctxt_cases] >>
          imp_res_tac evaluate_value_determ >>
          fs [ev_lem1] >>
          rw [] >>
          disj1_tac >|
          [qexists_tac `Lit (Num n2)`,
           qexists_tac `Lit (Num n2)`,
           qexists_tac `v2`,
           qexists_tac `v2`] >>
          rw [] >>
          once_rewrite_tac [evaluate_cases] >>
          rw [] >>
          once_rewrite_tac [evaluate_cases] >>
          rw [],
      all_tac,
      all_tac,
      all_tac,
      all_tac,
      all_tac],
 every_case_tac >>
     fs [return_def] >>
     rw [] >>
     fs [evaluate_state_cases] >>
     qpat_assum `evaluate cenv env (Con n vpat) bvpat`
          (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_cases]) >>
     fs [] >>
     rw [] >>
     fs [evaluate_ctxts_def, evaluate_ctxt_cases] >>
     rw [] >|
     [fs [Once evaluate_cases],
      fs [Once evaluate_cases],
      pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_cases]) >>
          fs [] >>
          rw [] >>
          disj1_tac >>
          qexists_tac `v` >>
          rw [] >>
          qexists_tac `Conv s (v::vs')` >>
          rw [] >>
          once_rewrite_tac [evaluate_cases] >>
          rw [] >>
          once_rewrite_tac [evaluate_cases] >>
          rw [] >>
          metis_tac [evaluate_value],
      pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_cases]) >>
          fs [] >>
          rw [] >>
          disj1_tac >>
          qexists_tac `v` >>
          rw [] >>
          qexists_tac `Conv s (v::vs')` >>
          rw [] >>
          once_rewrite_tac [evaluate_cases] >>
          rw [] >>
          once_rewrite_tac [evaluate_cases] >>
          rw [] >>
          metis_tac [evaluate_value]],
 every_case_tac >>
     fs [] >>
     rw [] >>
     fs [evaluate_state_cases] >>
     rw [] >>
     qpat_assum `evaluate cenv env (Var s) bvpat`
             (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_cases]) >>
     fs [] >>
     metis_tac [evaluate_value],
 fs [evaluate_state_cases] >>
     rw [] >>
     qpat_assum `evaluate cenv env (Fun s e'') bvpat`
             (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_cases]) >>
     fs [] >>
     metis_tac [evaluate_value],
 fs [evaluate_state_cases] >>
     rw [] >>
     qpat_assum `evaluate cenv env (App e' e0) bvpat`
             (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_cases]) >>
     fs [] >>
     rw [] >>
     fs [evaluate_ctxts_def, evaluate_ctxt_cases] >>
     rw [] >>
     metis_tac [evaluate_value],
 fs [evaluate_state_cases] >>
     rw [] >>
     qpat_assum `evaluate cenv env (Log l e' e0) bvpat`
             (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_cases]) >>
     fs [] >>
     rw [] >>
     fs [evaluate_ctxts_def, evaluate_ctxt_cases] >>
     rw [] >>
     disj1_tac >|
     [qexists_tac `Lit (Bool T)`,
      qexists_tac `v`,
      qexists_tac `Lit (Bool F)`,
      qexists_tac `v`,
      qexists_tac `Lit (Bool T)`,
      qexists_tac `Lit (Bool F)`] >>
     rw [] >>
     once_rewrite_tac [evaluate_cases] >>
     rw [] >>
     metis_tac [evaluate_value],
 fs [evaluate_state_cases] >>
     rw [] >>
     qpat_assum `evaluate cenv env (Op o' e' e0) bvpat`
             (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_cases]) >>
     fs [] >>
     rw [] >>
     fs [evaluate_ctxts_def, evaluate_ctxt_cases] >>
     rw [] >>
     disj1_tac >|
     [qexists_tac `Lit (Num n1)`,
      qexists_tac `Lit (Num n1)`,
      qexists_tac `v`,
      qexists_tac `v1`,
      qexists_tac `v1`] >>
     rw [] >>
     once_rewrite_tac [evaluate_cases] >>
     rw [] >>
     metis_tac [evaluate_value],
 fs [evaluate_state_cases] >>
     rw [] >>
     qpat_assum `evaluate cenv env (If e' e0 e1) bvpat`
             (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_cases]) >>
     fs [] >>
     rw [] >>
     fs [evaluate_ctxts_def, evaluate_ctxt_cases] >>
     rw [] >>
     disj1_tac >|
     [qexists_tac `Lit (Bool T)`,
      qexists_tac `Lit (Bool F)`,
      qexists_tac `Lit (Bool T)`,
      qexists_tac `Lit (Bool F)`,
      qexists_tac `v`] >>
     rw [] >>
     once_rewrite_tac [evaluate_cases] >>
     rw [] >>
     metis_tac [evaluate_value],
 fs [evaluate_state_cases] >>
     rw [] >>
     qpat_assum `evaluate cenv env (Mat e' l) bvpat`
             (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_cases]) >>
     fs [] >>
     rw [] >>
     fs [evaluate_ctxts_def, evaluate_ctxt_cases] >>
     rw [] >>
     disj1_tac >|
     [qexists_tac `v'`,
      qexists_tac `v`] >>
     rw [] >>
     once_rewrite_tac [evaluate_cases] >>
     rw [] >>
     metis_tac [evaluate_value],
 fs [evaluate_state_cases] >>
     rw [] >>
     qpat_assum `evaluate cenv env (Let s e' e0) bvpat`
             (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_cases]) >>
     fs [] >>
     rw [] >>
     fs [evaluate_ctxts_def, evaluate_ctxt_cases] >>
     rw [] >>
     disj1_tac >|
     [qexists_tac `v'`,
      qexists_tac `v`] >>
     rw [] >>
     once_rewrite_tac [evaluate_cases] >>
     rw [] >>
     metis_tac [evaluate_value],
 every_case_tac >>
     fs [evaluate_state_cases] >>
     rw [] >>
     qpat_assum `evaluate cenv env (Letrec l e') bvpat`
             (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_cases]) >>
     fs [] >>
     metis_tac []]
 *)


val _ = export_theory ();
