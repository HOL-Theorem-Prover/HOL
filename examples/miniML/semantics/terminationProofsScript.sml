open preamble;
open MiniMLTheory Print_astTheory (*CompileTheory*);
open intSimps;

val _ = new_theory "terminationProofs";

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

val (pos_int_to_string_def, pos_int_to_string_ind) =
  tprove_no_defn ((pos_int_to_string_def, pos_int_to_string_ind),
  wf_rel_tac `measure (\x.Num(ABS x))` >>
  rw [integerTheory.INT_ABS, integerTheory.int_gt] >-
  metis_tac [integerTheory.INT_LT_ANTISYM] >>
  fs [integerTheory.INT_NOT_LT] >>
  `?n'. n = &n'`
            by metis_tac [integerTheory.NUM_POSINT, integerTheory.INT_LT_IMP_LE]  >>
  rw [] >>
  fs []);
val _ = save_thm ("pos_int_to_string_def", pos_int_to_string_def);
val _ = save_thm ("pos_int_to_string_ind", pos_int_to_string_ind);

val (join_strings_def, join_strings_ind) =
  tprove_no_defn ((join_strings_def, join_strings_ind),
  wf_rel_tac `measure (\(_,x).LENGTH x)` >>
  srw_tac [ARITH_ss] []);
val _ = save_thm ("join_strings_def", join_strings_def);
val _ = save_thm ("join_strings_ind", join_strings_ind);

val (pat_to_string_def, pat_to_string_ind) =
  tprove_no_defn ((pat_to_string_def, pat_to_string_ind),
  wf_rel_tac `measure pat_size` >>
  rw [] >|
  [decide_tac,
   induct_on `v7` >>
       rw [] >>
       fs [pat_size_def] >>
       decide_tac,
   induct_on `ps` >>
       rw [] >>
       fs [pat_size_def] >>
       decide_tac]);
val _ = save_thm ("pat_to_string_def", pat_to_string_def);
val _ = save_thm ("pat_to_string_ind", pat_to_string_ind);

val (exp_to_string_def, exp_to_string_ind) =
  tprove_no_defn ((exp_to_string_def, exp_to_string_ind),
  wf_rel_tac `measure (\x. case x of INL e => exp_size e
                                   | INR (INL (p,e)) => exp_size e + 1
                                   | INR (INR (v1,v2,e)) => exp_size e + 1)` >>
  rw [] >>
  TRY (induct_on `funs`) >>
  TRY (induct_on `pes`) >>
  TRY (induct_on `es`) >>
  TRY (induct_on `v52`) >>
  rw [exp_size_def] >>
  fs [exp_size_def] >>
  rw [exp_size_def] >>
  decide_tac);
val _ = save_thm ("exp_to_string_def", exp_to_string_def);
val _ = save_thm ("exp_to_string_ind", exp_to_string_ind);

val (type_to_string_def, type_to_string_ind) =
  tprove_no_defn ((type_to_string_def, type_to_string_ind),
  wf_rel_tac `measure t_size` >>
  srw_tac [ARITH_ss] [] >>
  cases_on `ts` >>
  fs [] >>
  induct_on `t` >>
  rw [] >>
  fs [t_size_def] >>
  decide_tac);
val _ = save_thm ("type_to_string_def", type_to_string_def);
val _ = save_thm ("type_to_string_ind", type_to_string_ind);

val _ = export_theory ();
