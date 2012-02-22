open bossLib Theory Parse res_quanTheory Defn Tactic boolLib;
open finite_mapTheory listTheory pairTheory pred_setTheory;
open set_relationTheory sortingTheory stringTheory wordsTheory;
open relationTheory;
open MiniMLTheory CompileTheory;

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
  `inv_image $< (λx. case x of INL (a,p,b,c) => pat_size p | INR (a,ps,b,c) =>
  pat1_size ps)`);
val _ = save_thm ("pmatch_def", pmatch_def);
val _ = save_thm ("pmatch_ind", pmatch_ind);

val (pmatch'_def, pmatch'_ind) =
  tprove_no_defn ((pmatch'_def, pmatch'_ind),
  wf_rel_tac 
  `inv_image $< (λx. case x of INL (p,b,c) => pat_size p | INR (ps,b,c) =>
  pat1_size ps)`);
val _ = save_thm ("pmatch'_def", pmatch'_def);
val _ = save_thm ("pmatch'_ind", pmatch'_ind);

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

val (remove_ctors_def,remove_ctors_ind) =
  tprove_no_defn ((remove_ctors_def,remove_ctors_ind),
  WF_REL_TAC
  `inv_image $< (\x. case x of INL (x,y) => exp_size y 
                         | INR (INL (x,y)) => v_size y
                         | INR (INR (INL (x,y))) => exp3_size y
                         | INR (INR (INR (INL (x,y)))) => exp1_size y
                         | INR (INR (INR (INR (x,y)))) => exp6_size y)` >>
  rw [] >>
  TRY decide_tac >|
  [induct_on `es` >>
       rw [exp_size_def] >>
       res_tac >>
       decide_tac,
   induct_on `vs` >>
       rw [exp_size_def] >>
       res_tac >>
       decide_tac,
   induct_on `es` >>
       rw [exp_size_def] >>
       res_tac >>
       decide_tac]);
val _ = save_thm ("remove_ctors_def", remove_ctors_def);
val _ = save_thm ("remove_ctors_ind", remove_ctors_ind);



(* ------------------------------------------------------------------------- *)

(* Prove that the small step semantics never gets stuck if there is still work
 * to do (i.e., it must detect all type errors).  Thus, it either diverges or 
 * gives a result. *)

val untyped_safety_step = Q.prove (
`∀envC env ds st. 
  (d_step (envC, env, ds, st) = Dstuck) = (ds = []) ∧ (st = NONE)`,
rw [d_step_def, e_step_def, continue_def, push_def, return_def] >>
every_case_tac >>
fs [LET_THM, do_app_def] >>
every_case_tac >>
fs []);

val untyped_safety_thm = Q.store_thm ("untyped_safety_thm",
`!cenv env ds.
  diverges cenv env ds ∨ ?r. d_small_eval cenv env ds NONE r`,
rw [diverges_def, METIS_PROVE [] ``x ∨ y = ~x ⇒ y``, d_step_reln_def] >>
cases_on `d_step (cenv',env',ds',c')` >>
fs [untyped_safety_step] >|
[cases_on `p` >>
     cases_on `r` >> 
     cases_on `r'` >> 
     fs [],
 qexists_tac `Rerr (Rraise e)` >>
     rw [d_small_eval_def] >>
     metis_tac [],
 qexists_tac `Rerr Rtype_error` >>
     rw [d_small_eval_def] >>
     metis_tac [],
 qexists_tac `Rval env'` >>
     rw [d_small_eval_def] >>
     metis_tac []]);

val _ = export_theory ();
