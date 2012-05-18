open preamble intSimps;
open MiniMLTheory;

val _ = new_theory "MiniMLTermination";

(* ------------------ Termination proofs for MiniMLTheory ----------------- *)

val exp1_size_thm = store_thm(
"exp1_size_thm",
``∀ls. exp1_size ls = SUM (MAP exp2_size ls) + LENGTH ls``,
Induct >- rw[exp_size_def] >>
qx_gen_tac `p` >>
PairCases_on `p` >>
srw_tac [ARITH_ss][exp_size_def])

val exp3_size_thm = store_thm(
"exp3_size_thm",
``∀ls. exp3_size ls = SUM (MAP exp5_size ls) + LENGTH ls``,
Induct >- rw[exp_size_def] >>
Cases >> srw_tac[ARITH_ss][exp_size_def])

val exp6_size_thm = store_thm(
"exp6_size_thm",
``∀ls. exp6_size ls = SUM (MAP exp7_size ls) + LENGTH ls``,
Induct >- rw[exp_size_def] >>
Cases >> srw_tac [ARITH_ss][exp_size_def])

val exp8_size_thm = store_thm(
"exp8_size_thm",
``∀ls. exp8_size ls = SUM (MAP exp_size ls) + LENGTH ls``,
Induct >- rw[exp_size_def] >>
srw_tac [ARITH_ss][exp_size_def])

val exp9_size_thm = store_thm(
"exp9_size_thm",
``∀ls. exp9_size ls = SUM (MAP v_size ls) + LENGTH ls``,
Induct >- rw[exp_size_def] >>
srw_tac [ARITH_ss][exp_size_def])

val pat1_size_thm = store_thm(
"pat1_size_thm",
``∀ls. pat1_size ls = SUM (MAP pat_size ls) + LENGTH ls``,
Induct >- rw[pat_size_def] >>
srw_tac [ARITH_ss][pat_size_def])

val SUM_MAP_exp2_size_thm = store_thm(
"SUM_MAP_exp2_size_thm",
``∀defs. SUM (MAP exp2_size defs) = SUM (MAP (list_size char_size) (MAP FST defs)) +
                                    SUM (MAP exp4_size (MAP SND defs)) +
                                    LENGTH defs``,
Induct >- rw[exp_size_def] >>
qx_gen_tac `p` >>
PairCases_on `p` >>
srw_tac[ARITH_ss][exp_size_def])

val SUM_MAP_exp5_size_thm = store_thm(
"SUM_MAP_exp5_size_thm",
``∀env. SUM (MAP exp5_size env) = SUM (MAP (list_size char_size) (MAP FST env)) +
                                  SUM (MAP v_size (MAP SND env)) +
                                  LENGTH env``,
Induct >- rw[exp_size_def] >>
Cases >> srw_tac[ARITH_ss][exp_size_def])

val SUM_MAP_exp4_size_thm = store_thm(
"SUM_MAP_exp4_size_thm",
``∀ls. SUM (MAP exp4_size ls) = SUM (MAP (list_size char_size) (MAP FST ls)) +
                                SUM (MAP exp_size (MAP SND ls)) +
                                LENGTH ls``,
Induct >- rw[exp_size_def] >>
Cases >> srw_tac[ARITH_ss][exp_size_def])

val SUM_MAP_exp7_size_thm = store_thm(
"SUM_MAP_exp7_size_thm",
``∀ls. SUM (MAP exp7_size ls) = SUM (MAP pat_size (MAP FST ls)) +
                                SUM (MAP exp_size (MAP SND ls)) +
                                LENGTH ls``,
Induct >- rw[exp_size_def] >>
Cases >> srw_tac[ARITH_ss][exp_size_def])

val exp_size_positive = store_thm(
"exp_size_positive",
``∀e. 0 < exp_size e``,
Induct >> srw_tac[ARITH_ss][exp_size_def])
val _ = export_rewrites["exp_size_positive"];

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
val _ = export_rewrites["lookup_def"];

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

val (deBruijn_subst_def, deBruijn_subst_ind) =
  tprove_no_defn ((deBruijn_subst_def, deBruijn_subst_ind),
  WF_REL_TAC `measure (λ(x,y). t_size y)` >>
  rw [] >|
  [induct_on `ts` >>
       rw [t_size_def] >>
       res_tac >>
       decide_tac,
   decide_tac,
   decide_tac]);
val _ = register "deBruijn_subst" deBruijn_subst_def deBruijn_subst_ind;

val (enough_tvars_def, enough_tvars_ind) =
  tprove_no_defn ((enough_tvars_def, enough_tvars_ind),
  WF_REL_TAC `measure (λ(x,y). t_size y)` >>
  rw [] >|
  [induct_on `ts` >>
       rw [t_size_def] >>
       res_tac >>
       decide_tac,
   decide_tac,
   decide_tac]);
val _ = register "enough_tvars" enough_tvars_def enough_tvars_ind;

val (is_source_exp_def,is_source_exp_ind) =
  tprove_no_defn ((is_source_exp_def,is_source_exp_ind),
  WF_REL_TAC `measure exp_size` >>
  srw_tac[ARITH_ss][exp1_size_thm,exp6_size_thm,exp8_size_thm] >>
  map_every (fn q =>
    TRY (Q.ISPEC_THEN q imp_res_tac SUM_MAP_MEM_bound))
  [`exp2_size`,`exp7_size`,`exp_size`] >>
  fsrw_tac[ARITH_ss][exp_size_def])
val _ = register "is_source_exp" is_source_exp_def is_source_exp_ind;
val _ = export_rewrites["is_source_exp_def"];

val (check_freevars_def,check_freevars_ind) =
  tprove_no_defn ((check_freevars_def,check_freevars_ind),
wf_rel_tac `measure (t_size o SND o SND)` >>
srw_tac [ARITH_ss] [t_size_def] >>
induct_on `ts` >>
srw_tac [ARITH_ss] [t_size_def] >>
res_tac >>
decide_tac);
val _ = register "check_freevars" check_freevars_def check_freevars_ind;

val _ = export_theory ();
