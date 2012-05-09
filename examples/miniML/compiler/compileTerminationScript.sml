open MiniMLTheory MiniMLTerminationTheory
open HolKernel boolLib bossLib Defn CompileTheory listTheory lcsymtacs
val _ = new_theory "compileTermination"

(* size helper theorems *)

val MEM_pair_MAP = store_thm(
"MEM_pair_MAP",
``MEM (a,b) ls ==> MEM a (MAP FST ls) /\ MEM b (MAP SND ls)``,
rw[MEM_MAP,pairTheory.EXISTS_PROD] >> PROVE_TAC[])

val Cexp1_size_thm = store_thm(
"Cexp1_size_thm",
``∀ls. Cexp1_size ls = SUM (MAP Cexp2_size ls) + LENGTH ls``,
Induct >- rw[Cexp_size_def] >>
qx_gen_tac `p` >>
PairCases_on `p` >>
srw_tac [ARITH_ss][Cexp_size_def])

val tac = Induct >- rw[Cexp_size_def,Cpat_size_def] >> srw_tac [ARITH_ss][Cexp_size_def,Cpat_size_def]
fun tm t1 t2 =  ``∀ls. ^t1 ls = SUM (MAP ^t2 ls) + LENGTH ls``
fun size_thm name t1 t2 = store_thm(name,tm t1 t2,tac)
val Cexp3_size_thm = size_thm "Cexp3_size_thm" ``Cexp3_size`` ``Cexp5_size``
val Cexp4_size_thm = size_thm "Cexp4_size_thm" ``Cexp4_size`` ``Cexp6_size``
val Cexp7_size_thm = size_thm "Cexp7_size_thm" ``Cexp7_size`` ``Cexp_size``
val Cexp8_size_thm = size_thm "Cexp8_size_thm" ``Cexp8_size`` ``Cv_size``
val Cpat1_size_thm = size_thm "Cpat1_size_thm" ``Cpat1_size`` ``Cpat_size``

val SUM_MAP_Cexp2_size_thm = store_thm(
"SUM_MAP_Cexp2_size_thm",
``∀env. SUM (MAP Cexp2_size env) =
  SUM (MAP (list_size (λx. x)) (MAP FST env))
+ SUM (MAP Cexp_size (MAP SND env))
+ LENGTH env``,
Induct >- rw[Cexp_size_def] >> Cases >>
srw_tac[ARITH_ss][Cexp_size_def])

val SUM_MAP_Cexp5_size_thm = store_thm(
"SUM_MAP_Cexp5_size_thm",
``∀env. SUM (MAP Cexp5_size env) =
  SUM (MAP FST env)
+ SUM (MAP Cv_size (MAP SND env))
+ LENGTH env``,
Induct >- rw[Cexp_size_def] >> Cases >>
srw_tac[ARITH_ss][Cexp_size_def])

val SUM_MAP_Cexp6_size_thm = store_thm(
"SUM_MAP_Cexp6_size_thm",
``∀env. SUM (MAP Cexp6_size env) =
  SUM (MAP Cpat_size (MAP FST env))
+ SUM (MAP Cexp_size (MAP SND env))
+ LENGTH env``,
Induct >- rw[Cexp_size_def] >> Cases >>
srw_tac[ARITH_ss][Cexp_size_def])

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

(* semantics definitions *)

fun register name (def,ind) = let
  val _ = save_thm(name^"_def", def)
  val _ = save_thm(name^"_ind", ind)
in (def,ind) end

val Cevaluate_cases = save_thm("Cevaluate_cases",Cevaluate_cases)
val Cevaluate_rules = save_thm("Cevaluate_rules",Cevaluate_rules)
val extend_def = save_thm("extend_def",extend_def)
val exp_Cexp_ind = save_thm("exp_Cexp_ind",exp_Cexp_ind)
val v_Cv_ind = save_thm("v_Cv_ind",v_Cv_ind)
val v_Cv_cases = save_thm("v_Cv_cases",v_Cv_cases)
val sort_Cenv_def = save_thm("sort_Cenv_def",sort_Cenv_def)
val i0_def = save_thm("i0_def",i0_def)
val Cevaluate_ind = save_thm("Cevaluate_ind",Cevaluate_ind)
val Cevaluate_strongind = save_thm("Cevaluate_strongind",Cevaluate_strongind)
val mk_env_def = save_thm("mk_env_def",mk_env_def)
val find_index_def = save_thm("find_index_def",find_index_def)
val Cexp_size_def = save_thm("Cexp_size_def",Cexp_size_def)

val (free_vars_def, free_vars_ind) = register "free_vars" (
  tprove_no_defn ((free_vars_def,free_vars_ind),
  WF_REL_TAC `measure Cexp_size` >>
  srw_tac[ARITH_ss][Cexp1_size_thm,Cexp4_size_thm,Cexp7_size_thm] >>
  MAP_EVERY (fn q => Q.ISPEC_THEN q mp_tac SUM_MAP_MEM_bound)
  [`Cexp_size`,`Cexp2_size`,`Cexp6_size`] >>
  rw[] >> res_tac >> fs[Cexp_size_def] >> srw_tac[ARITH_ss][]))
val _ = export_rewrites["free_vars_def"];

val (inst_arg_def,inst_arg_ind) = register "inst_arg" (
  tprove_no_defn ((inst_arg_def,inst_arg_ind),
  WF_REL_TAC `measure (nt_size o SND)` >>
  rw[nt1_size_thm] >>
  Q.ISPEC_THEN `nt_size` imp_res_tac SUM_MAP_MEM_bound >>
  srw_tac[ARITH_ss][]))

val (Cpat_vars_def,Cpat_vars_ind) = register "Cpat_vars" (
  tprove_no_defn ((Cpat_vars_def,Cpat_vars_ind),
  WF_REL_TAC `measure Cpat_size` >>
  rw[Cpat1_size_thm] >>
  imp_res_tac SUM_MAP_MEM_bound >>
  pop_assum (qspec_then `Cpat_size` mp_tac) >>
  srw_tac[ARITH_ss][]))
val _ = export_rewrites["Cpat_vars_def"]

val (Cv_to_ov_def,Cv_to_ov_ind) = register "Cv_to_ov" (
  tprove_no_defn ((Cv_to_ov_def,Cv_to_ov_ind),
  WF_REL_TAC `measure (Cv_size o SND)` >>
  rw[Cexp8_size_thm] >>
  Q.ISPEC_THEN `Cv_size` imp_res_tac SUM_MAP_MEM_bound >>
  srw_tac[ARITH_ss][]))
val _ = export_rewrites["Cv_to_ov_def"];

val (v_to_ov_def,v_to_ov_ind) = register "v_to_ov" (
  tprove_no_defn ((v_to_ov_def,v_to_ov_ind),
  WF_REL_TAC `measure v_size` >>
  rw[exp9_size_thm] >>
  Q.ISPEC_THEN `v_size` imp_res_tac SUM_MAP_MEM_bound >>
  srw_tac[ARITH_ss][]))
val _ = export_rewrites["v_to_ov_def"];

val _ = save_thm ("map_result_def", map_result_def);
val _ = export_rewrites["map_result_def"];

val _ = save_thm ("Cmatch_map_def", Cmatch_map_def);
val _ = export_rewrites["Cmatch_map_def"];

val _ = save_thm ("Cmatch_bind_def", Cmatch_bind_def);
val _ = export_rewrites["Cmatch_bind_def"];

val _ = save_thm ("doPrim2_def", doPrim2_def);
val _ = export_rewrites["doPrim2_def"];

val _ = save_thm ("CevalPrim2_def", CevalPrim2_def);
val _ = export_rewrites["CevalPrim2_def"];

val (Cpmatch_def,Cpmatch_ind) = register "Cpmatch" (
  tprove_no_defn ((Cpmatch_def,Cpmatch_ind),
  WF_REL_TAC `inv_image $<
                (λx. case x of
                     | (INL (env,p,v)) => Cv_size v
                     | (INR (env,ps,vs)) => Cexp8_size vs)`))

val (ce_Cexp_def,ce_Cexp_ind) = register "ce_Cexp"(
  tprove_no_defn ((ce_Cexp_def,ce_Cexp_ind),
  WF_REL_TAC `inv_image $<
                (λx. case x of
                     | (INL e) => Cexp_size e
                     | (INR v) => Cv_size v)` >>
  srw_tac[ARITH_ss][Cexp1_size_thm,Cexp3_size_thm,Cexp4_size_thm,Cexp7_size_thm,Cexp8_size_thm,SUM_MAP_Cexp2_size_thm,SUM_MAP_Cexp5_size_thm,SUM_MAP_Cexp6_size_thm] >>
  imp_res_tac MEM_pair_MAP >>
  Q.ISPEC_THEN `Cexp_size` imp_res_tac SUM_MAP_MEM_bound >>
  Q.ISPEC_THEN `Cv_size` imp_res_tac SUM_MAP_MEM_bound >>
  fsrw_tac[ARITH_ss][Cexp_size_def]))
val _ = export_rewrites["ce_Cexp_def"]

(* compiler definitions *)

val (remove_mat_def,remove_mat_ind) = register "remove_mat" (
  tprove_no_defn ((remove_mat_def,remove_mat_ind),
  WF_REL_TAC
  `inv_image $<
    (λx. case x of
         | INL e => Cexp_size e
         | INR (_,pes) => Cexp4_size pes)` >>
  srw_tac[ARITH_ss][Cexp1_size_thm,Cexp4_size_thm,Cexp7_size_thm] >>
  MAP_EVERY (fn q => Q.ISPEC_THEN q mp_tac SUM_MAP_MEM_bound) [`Cexp_size`,`Cexp2_size`,`Cexp7_size`] >>
  rw[] >> res_tac >> fs[Cexp_size_def] >> srw_tac[ARITH_ss][]))

val (exp_to_Cexp_def,exp_to_Cexp_ind) = register "exp_to_Cexp" (
  tprove_no_defn ((exp_to_Cexp_def,exp_to_Cexp_ind),
  WF_REL_TAC `inv_image ($< LEX $<) (λx. case x of
    | INL (_,e) => (exp_size e, 0:num)
    | INR (INL (_,defs,_)) => (exp1_size defs, 0)
    | INR (INR (INL (_,e,_))) => (exp_size e, 1)
    | INR (INR (INR (_,v))) => (v_size v, 0))` >>
  srw_tac[ARITH_ss][exp1_size_thm,exp3_size_thm,exp6_size_thm,exp8_size_thm,exp9_size_thm] >>
  MAP_EVERY (fn q => Q.ISPEC_THEN q mp_tac SUM_MAP_MEM_bound) [`exp2_size`,`exp5_size`,`exp7_size`,`exp_size`,`v_size`] >>
  rw[] >> res_tac >> fs[exp_size_def] >> srw_tac[ARITH_ss][]))

val pat_to_Cpat_def = save_thm("pat_to_Cpat_def",pat_to_Cpat_def)

val (compile_varref_def, compile_varref_ind) = register "compile_varref" (
  tprove_no_defn ((compile_varref_def, compile_varref_ind),
  WF_REL_TAC `measure (λp. case p of (_,CTEnv _) => 0 | (_,CTRef _) => 1)`))

val (compile_def, compile_ind) = register "compile" (
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
   Cases_on `nso` >> fsrw_tac[ARITH_ss][Cexp_size_def])))

val (replace_calls_def,replace_calls_ind) = register "replace_calls" (
  tprove_no_defn ((replace_calls_def,replace_calls_ind),
  WF_REL_TAC `measure (LENGTH o FST o SND)` >> rw[] ))

val (number_constructors_def,number_constructors_ind) = register "number_constructors" (
  tprove_no_defn ((number_constructors_def,number_constructors_ind),
  WF_REL_TAC `measure (LENGTH o SND o SND o SND)` >> rw[]))

val (repl_dec_def,repl_dec_ind) = register "repl_dec" (
  tprove_no_defn ((repl_dec_def,repl_dec_ind),
  WF_REL_TAC `measure (dec_size o SND)`))

val (bcv_to_ov_def,bcv_to_ov_ind) = register "bcv_to_ov" (
  tprove_no_defn ((bcv_to_ov_def,bcv_to_ov_ind),
  WF_REL_TAC `measure (bc_value_size o SND o SND)` >>
  rw[bc_value1_size_thm] >>
  Q.ISPEC_THEN `bc_value_size` imp_res_tac SUM_MAP_MEM_bound >>
  srw_tac[ARITH_ss][]))

val (fold_num_def,fold_num_ind) = register "fold_num" (
  tprove_no_defn ((fold_num_def,fold_num_ind),
  WF_REL_TAC `measure (SND o SND)`))

val _ = export_theory()
