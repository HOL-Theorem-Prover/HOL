open preamble;
open MiniMLTheory Print_astTheory;
open intSimps;

val _ = new_theory "terminationProofs";

(* --------------------- Termination proofs -------------------------------- *)

fun register name def ind = 
  let val _ = save_thm (name ^ "_def", def);
      val _ = save_thm (name ^ "_ind", ind);
      val _ = computeLib.add_persistent_funs [(name ^ "_def", def)];
  in
    ()
  end

val (lookup_def, lookup_ind) =
  tprove_no_defn ((lookup_def, lookup_ind),
  WF_REL_TAC `measure (λ(x,y). LENGTH y)` >>
  rw []);
val _ = register "lookup" lookup_def lookup_ind;

val (pmatch_def, pmatch_ind) =
  tprove_no_defn ((pmatch_def, pmatch_ind),
  wf_rel_tac
  `inv_image $< (λx. case x of INL (a,p,b,c) => pat_size p | INR (a,ps,b,c) =>
  pat1_size ps)`);
val _ = register "pmatch" pmatch_def pmatch_ind;

val (pmatch'_def, pmatch'_ind) =
  tprove_no_defn ((pmatch'_def, pmatch'_ind),
  wf_rel_tac
  `inv_image $< (λx. case x of INL (p,b,c) => pat_size p | INR (ps,b,c) =>
  pat1_size ps)`);
val _ = register "pmatch'" pmatch'_def pmatch'_ind;

val (find_recfun_def, find_recfun_ind) =
  tprove_no_defn ((find_recfun_def, find_recfun_ind),
  WF_REL_TAC `measure (λ(x,y). LENGTH y)` >>
  rw []);
val _ = register "find_recfun" find_recfun_def find_recfun_ind;

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
val _ = register "type_subst" type_subst_def type_subst_ind;

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
val _ = register "pos_int_to_string" pos_int_to_string_def pos_int_to_string_ind;

val (join_strings_def, join_strings_ind) =
  tprove_no_defn ((join_strings_def, join_strings_ind),
  wf_rel_tac `measure (\(_,x).LENGTH x)` >>
  srw_tac [ARITH_ss] []);
val _ = register "join_strings" join_strings_def join_strings_ind;

val (pat_to_stree_def, pat_to_stree_ind) =
  tprove_no_defn ((pat_to_stree_def, pat_to_stree_ind),
  wf_rel_tac `measure (\(_,x). pat_size x)` >>
  rw [] >|
  [induct_on `ps` >>
       rw [] >>
       fs [pat_size_def] >>
       decide_tac,
   decide_tac,
   induct_on `v9` >>
       rw [] >>
       fs [pat_size_def] >>
       decide_tac]);
val _ = register "pat_to_stree" pat_to_stree_def pat_to_stree_ind;

val (exp_to_stree_def, exp_to_stree_ind) =
  tprove_no_defn ((exp_to_stree_def, exp_to_stree_ind),
  wf_rel_tac `measure (\x. case x of INL (_,_,e) => exp_size e
                                   | INR (INL (_,_,p,e)) => exp_size e + 1
                                   | INR (INR (_,_,v1,v2,e)) => exp_size e + 1)` >>
  rw [] >>
  TRY (induct_on `funs`) >>
  TRY (induct_on `pes`) >>
  TRY (induct_on `es`) >>
  TRY (induct_on `v56`) >>
  rw [exp_size_def] >>
  fs [exp_size_def] >>
  rw [exp_size_def] >>
  decide_tac);
val _ = register "exp_to_stree" exp_to_stree_def exp_to_stree_ind;

val (type_to_stree_def, type_to_stree_ind) =
  tprove_no_defn ((type_to_stree_def, type_to_stree_ind),
  wf_rel_tac `measure t_size` >>
  srw_tac [ARITH_ss] [] >>
  cases_on `ts` >>
  fs [] >>
  induct_on `t` >>
  rw [] >>
  fs [t_size_def] >>
  decide_tac);
val _ = register "type_to_stree" type_to_stree_def type_to_stree_ind;

val _ = export_theory ();
