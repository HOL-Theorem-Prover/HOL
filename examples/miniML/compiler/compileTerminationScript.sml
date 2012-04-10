open MiniMLTheory
open HolKernel boolLib bossLib Defn CompileTheory listTheory lcsymtacs
val _ = new_theory "compileTermination"

(* move elsewhere? *)
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

val exp_size_positive = store_thm(
"exp_size_positive",
``∀e. 0 < exp_size e``,
Induct >> srw_tac[ARITH_ss][exp_size_def])
val _ = export_rewrites["exp_size_positive"]

(* size helper theorems *)

val Cexp1_size_thm = store_thm(
"Cexp1_size_thm",
``∀ls. Cexp1_size ls = SUM (MAP Cexp2_size ls) + LENGTH ls``,
Induct >- rw[Cexp_size_def] >>
qx_gen_tac `p` >>
PairCases_on `p` >>
srw_tac [ARITH_ss][Cexp_size_def])

val Cexp4_size_thm = store_thm(
"Cexp4_size_thm",
``∀ls. Cexp4_size ls = SUM (MAP Cexp6_size ls) + LENGTH ls``,
Induct >- rw[Cexp_size_def] >>
srw_tac [ARITH_ss][Cexp_size_def])

val Cexp7_size_thm = store_thm(
"Cexp7_size_thm",
``∀ls. Cexp7_size ls = SUM (MAP Cexp_size ls) + LENGTH ls``,
Induct >- rw[Cexp_size_def] >>
srw_tac [ARITH_ss][Cexp_size_def])

val Cexp8_size_thm = store_thm(
"Cexp8_size_thm",
``∀ls. Cexp8_size ls = SUM (MAP Cv_size ls) + LENGTH ls``,
Induct >- rw[Cexp_size_def] >>
srw_tac [ARITH_ss][Cexp_size_def])

val list_size_thm = store_thm(
"list_size_thm",
``∀f ls. list_size f ls = SUM (MAP f ls) + LENGTH ls``,
gen_tac >> Induct >> srw_tac[ARITH_ss][list_size_def])

val bc_value1_size_thm = store_thm(
"bc_value1_size_thm",
``∀ls. bc_value1_size ls = SUM (MAP bc_value_size ls) + LENGTH ls``,
Induct >- rw[BytecodeTheory.bc_value_size_def] >>
srw_tac [ARITH_ss][BytecodeTheory.bc_value_size_def])

val nt1_size_thm = store_thm(
"nt1_size_thm",
``∀ls. nt1_size ls = SUM (MAP nt_size ls) + LENGTH ls``,
Induct >- rw[nt_size_def] >>
srw_tac [ARITH_ss][nt_size_def])

(* compiler definitions *)

val (remove_mat_def,remove_mat_ind) =
  tprove_no_defn ((remove_mat_def,remove_mat_ind),
  WF_REL_TAC
  `inv_image $<
    (λx. case x of
         | INL e => Cexp_size e
         | INR (v,pes) => Cexp4_size pes)` >>
  srw_tac[ARITH_ss][Cexp1_size_thm,Cexp4_size_thm,Cexp7_size_thm] >>
  MAP_EVERY (fn q => Q.ISPEC_THEN q mp_tac SUM_MAP_MEM_bound) [`Cexp_size`,`Cexp2_size`,`Cexp7_size`] >>
  rw[] >> res_tac >> fs[Cexp_size_def] >> srw_tac[ARITH_ss][])
val _ = save_thm ("remove_mat_def", remove_mat_def);
val _ = save_thm ("remove_mat_ind", remove_mat_ind);

val (exp_to_Cexp_def,exp_to_Cexp_ind) =
  tprove_no_defn ((exp_to_Cexp_def,exp_to_Cexp_ind),
  WF_REL_TAC `measure (exp_size o SND o SND o SND)` >>
  srw_tac[ARITH_ss][exp1_size_thm,exp8_size_thm,exp6_size_thm] >>
  MAP_EVERY (fn q => Q.ISPEC_THEN q mp_tac SUM_MAP_MEM_bound) [`exp7_size`,`exp_size`,`exp2_size`] >>
  rw[] >> res_tac >> fs[exp_size_def] >> srw_tac[ARITH_ss][])
val _ = save_thm ("exp_to_Cexp_def", exp_to_Cexp_def);
val _ = save_thm ("exp_to_Cexp_ind", exp_to_Cexp_ind);

val (free_vars_def, free_vars_ind) =
  tprove_no_defn ((free_vars_def,free_vars_ind),
  WF_REL_TAC `measure Cexp_size` >>
  srw_tac[ARITH_ss][Cexp1_size_thm,Cexp4_size_thm,Cexp7_size_thm] >>
  MAP_EVERY (fn q => Q.ISPEC_THEN q mp_tac SUM_MAP_MEM_bound)
  [`Cexp_size`,`Cexp2_size`,`Cexp6_size`] >>
  rw[] >> res_tac >> fs[Cexp_size_def] >> srw_tac[ARITH_ss][])
val _ = save_thm ("free_vars_def", free_vars_def);
val _ = save_thm ("free_vars_ind", free_vars_ind);

val (pat_to_Cpat_def, pat_to_Cpat_ind) =
  tprove_no_defn ((pat_to_Cpat_def,pat_to_Cpat_ind),
  WF_REL_TAC `measure (pat_size o SND o SND o SND)` >>
  srw_tac [ARITH_ss][pat1_size_thm] >>
  imp_res_tac SUM_MAP_MEM_bound >>
  pop_assum (qspec_then `pat_size` mp_tac) >>
  srw_tac[ARITH_ss][])
val _ = save_thm ("pat_to_Cpat_def", pat_to_Cpat_def);
val _ = save_thm ("pat_to_Cpat_ind", pat_to_Cpat_ind);

val (compile_varref_def, compile_varref_ind) =
  tprove_no_defn ((compile_varref_def, compile_varref_ind),
  WF_REL_TAC `measure (λp. case p of (_,CTEnv _) => 0 | (_,CTRef _) => 1)`)
val _ = save_thm ("compile_varref_def", compile_varref_def);
val _ = save_thm ("compile_varref_ind", compile_varref_ind);

val (compile_def, compile_ind) =
  tprove_no_defn ((compile_def, compile_ind),
  WF_REL_TAC `inv_image ($< LEX $<) (λx. case x of
       | INL (s,e)                 => (Cexp_size e, 3:num)
       | INR (INL (env,z,e,n,s,[]))=> (Cexp_size e, 4)
       | INR (INL (env,z,e,n,s,ns))=> (Cexp_size e + (SUM ns) + LENGTH ns, 2)
       | INR (INR (NONE,s,xbs))    => (SUM (MAP Cexp2_size xbs), 1)
       | INR (INR (SOME ns,s,xbs)) => (SUM (MAP Cexp2_size xbs) + (SUM ns) + LENGTH ns, 0))` >>
  srw_tac[ARITH_ss][] >>
  srw_tac[ARITH_ss][Cexp1_size_thm,Cexp4_size_thm,Cexp_size_def,Cexp7_size_thm,list_size_thm] >>
  TRY (Q.ISPEC_THEN `Cexp_size` imp_res_tac SUM_MAP_MEM_bound >> DECIDE_TAC) >>
  TRY (Cases_on `xs` >> srw_tac[ARITH_ss][]) >>
  TRY (Cases_on `ns` >> srw_tac[ARITH_ss][]) >>
  (Q.ISPEC_THEN `Cexp2_size` imp_res_tac SUM_MAP_MEM_bound >>
   Cases_on `nso` >> fsrw_tac[ARITH_ss][Cexp_size_def]))
val _ = save_thm ("compile_def", compile_def);
val _ = save_thm ("compile_ind", compile_ind);

val (replace_calls_def,replace_calls_ind) =
  tprove_no_defn ((replace_calls_def,replace_calls_ind),
  WF_REL_TAC `measure (LENGTH o FST o SND)` >> rw[] )
val _ = save_thm ("replace_calls_def", replace_calls_def);
val _ = save_thm ("replace_calls_ind", replace_calls_ind);

val (number_constructors_def,number_constructors_ind) =
  tprove_no_defn ((number_constructors_def,number_constructors_ind),
  WF_REL_TAC `measure (LENGTH o SND o SND o SND)` >> rw[])
val _ = save_thm ("number_constructors_def", number_constructors_def);
val _ = save_thm ("number_constructors_ind", number_constructors_ind);

val (repl_dec_def,repl_dec_ind) =
  tprove_no_defn ((repl_dec_def,repl_dec_ind),
  WF_REL_TAC `measure (dec_size o SND)`)
val _ = save_thm ("repl_dec_def", repl_dec_def);
val _ = save_thm ("repl_dec_ind", repl_dec_ind);

val (bcv_to_ov_def,bcv_to_ov_ind) =
  tprove_no_defn ((bcv_to_ov_def,bcv_to_ov_ind),
  WF_REL_TAC `measure (bc_value_size o SND o SND)` >>
  rw[bc_value1_size_thm] >>
  Q.ISPEC_THEN `bc_value_size` imp_res_tac SUM_MAP_MEM_bound >>
  srw_tac[ARITH_ss][])
val _ = save_thm ("bcv_to_ov_def", bcv_to_ov_def);
val _ = save_thm ("bcv_to_ov_ind", bcv_to_ov_ind);

val (inst_arg_def,inst_arg_ind) =
  tprove_no_defn ((inst_arg_def,inst_arg_ind),
  WF_REL_TAC `measure (nt_size o SND)` >>
  rw[nt1_size_thm] >>
  Q.ISPEC_THEN `nt_size` imp_res_tac SUM_MAP_MEM_bound >>
  srw_tac[ARITH_ss][])
val _ = save_thm ("inst_arg_def", inst_arg_def);
val _ = save_thm ("inst_arg_ind", inst_arg_ind);

val (fold_num_def,fold_num_ind) =
  tprove_no_defn ((fold_num_def,fold_num_ind),
  WF_REL_TAC `measure (SND o SND)`)
val _ = save_thm ("fold_num_def", fold_num_def);
val _ = save_thm ("fold_num_ind", fold_num_ind);

val (pat_vars_def,pat_vars_ind) =
  tprove_no_defn ((pat_vars_def,pat_vars_ind),
  WF_REL_TAC `measure pat_size` >>
  rw[pat1_size_thm] >>
  imp_res_tac SUM_MAP_MEM_bound >>
  pop_assum (qspec_then `pat_size` mp_tac) >>
  srw_tac[ARITH_ss][])
val _ = save_thm ("pat_vars_def", pat_vars_def);
val _ = save_thm ("pat_vars_ind", pat_vars_ind);

val (Cv_to_ov_def,Cv_to_ov_ind) =
  tprove_no_defn ((Cv_to_ov_def,Cv_to_ov_ind),
  WF_REL_TAC `measure (Cv_size o SND)` >>
  rw[Cexp8_size_thm] >>
  Q.ISPEC_THEN `Cv_size` imp_res_tac SUM_MAP_MEM_bound >>
  srw_tac[ARITH_ss][])
val _ = save_thm ("Cv_to_ov_def", Cv_to_ov_def);
val _ = save_thm ("Cv_to_ov_ind", Cv_to_ov_ind);
val _ = export_rewrites["Cv_to_ov_def"];

val (v_to_ov_def,v_to_ov_ind) =
  tprove_no_defn ((v_to_ov_def,v_to_ov_ind),
  WF_REL_TAC `measure v_size` >>
  rw[exp9_size_thm] >>
  Q.ISPEC_THEN `v_size` imp_res_tac SUM_MAP_MEM_bound >>
  srw_tac[ARITH_ss][])
val _ = save_thm ("v_to_ov_def", v_to_ov_def);
val _ = save_thm ("v_to_ov_ind", v_to_ov_ind);
val _ = export_rewrites["v_to_ov_def"];

val _ = save_thm ("map_result_def", map_result_def);
val _ = export_rewrites["map_result_def"];

val _ = export_theory()
