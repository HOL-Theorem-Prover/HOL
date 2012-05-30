open HolKernel bossLib boolLib listTheory pred_setTheory finite_mapTheory alistTheory lcsymtacs
open SatisfySimps boolSimps compileTerminationTheory intLangTheory

val _ = new_theory "compileCorrectness"

(* Invariants *)

val good_cm_cw_def = Define`
  good_cm_cw cm cw =
  (FDOM cw = FRANGE cm) ∧
  (FRANGE cw = FDOM cm) ∧
  (∀x. x ∈ FDOM cm ⇒ (cw ' (cm ' x) = x)) ∧
  (∀y. y ∈ FDOM cw ⇒ (cm ' (cw ' y) = y))`

val good_cmaps_def = Define`
good_cmaps cenv cm cw =
  (∀cn n. do_con_check cenv cn n ⇒ cn IN FDOM cm) ∧
  good_cm_cw cm cw`

(*
val observable_v_def = tDefine "observable_v"`
  (observable_v (Lit l) = T) ∧
  (observable_v (Conv cn vs) = EVERY observable_v vs) ∧
  (observable_v _ = F)`(
WF_REL_TAC `measure v_size` >>
rw[MiniMLTerminationTheory.exp9_size_thm] >>
Q.ISPEC_THEN `v_size` imp_res_tac SUM_MAP_MEM_bound >>
srw_tac[ARITH_ss][])
val _ = export_rewrites["observable_v_def"]

val observable_Cv_def = tDefine "observable_Cv"`
  (observable_Cv (CLit l) = T) ∧
  (observable_Cv (CConv cn vs) = EVERY observable_Cv vs) ∧
  (observable_Cv _ = F)`(
WF_REL_TAC `measure Cv_size` >>
rw[Cexp8_size_thm] >>
Q.ISPEC_THEN `Cv_size` imp_res_tac SUM_MAP_MEM_bound >>
srw_tac[ARITH_ss][])
val _ = export_rewrites["observable_Cv_def"]
*)

val good_G_def = Define`
  good_G G =
    (∀cm v Cv. v_Cv G cm v Cv ⇒ G cm v Cv) ∧
    (∀cm v Cv cw.
      good_cm_cw cm cw ∧
      G cm v Cv ⇒ ((v_to_ov v) = (Cv_to_ov cw) Cv))`

val a_good_G_exists = store_thm(
"a_good_G_exists",
``∃G. good_G G``,
qexists_tac `v_Cv (K (K (K F)))` >>
rw[good_G_def] >- (
  qsuff_tac `∀G cm v Cv. v_Cv G cm v Cv ⇒ (G = v_Cv (K(K(K F)))) ⇒ v_Cv (K(K(K F))) cm v Cv` >- rw[] >>
  ho_match_mp_tac v_Cv_ind >>
  rw[] >>
  rw[v_Cv_cases] >>
  fsrw_tac[boolSimps.ETA_ss][] ) >>
qsuff_tac `∀G cm v Cv. v_Cv G cm v Cv ⇒ (G = K(K(K F))) ∧ good_cm_cw cm cw ⇒ (v_to_ov v = Cv_to_ov cw Cv)` >- (rw[] >> PROVE_TAC[]) >>
ho_match_mp_tac v_Cv_ind >>
rw[] >- fs[good_cm_cw_def] >>
pop_assum mp_tac >>
srw_tac[boolSimps.ETA_ss][] >>
rw[MAP_EQ_EVERY2] >>
PROVE_TAC[EVERY2_LENGTH])

val good_envs_def = Define`
  good_envs env s s' Cenv = s.cmap SUBMAP s'.cmap`

val good_cmap_def = Define`
good_cmap cenv cm =
  (∀cn n. do_con_check cenv cn n ⇒ cn IN FDOM cm)`

(* Soundness(?) of exp_Cexp *)

(*
val exp_Cexp_thm = store_thm(
"exp_Cexp_thm",``
∀G cm env Cenv exp Cexp. exp_Cexp G cm env Cenv exp Cexp ⇒
  good_G G ⇒
  ∀cenv res.
    evaluate cenv env exp res ⇒
    ∀cw. good_cmaps cenv cm cw ⇒
      ∃Cres.
        Cevaluate Cenv Cexp Cres ∧
        (map_result (Cv_to_ov cw) Cres =
         map_result v_to_ov res)``,
ho_match_mp_tac exp_Cexp_ind >>
rw[] >- (
  fs[good_G_def,good_cmaps_def] >>
  PROVE_TAC[] )
>- (
  fs[EVERY2_EVERY,EVERY_MEM] >>
  qpat_assum `LENGTH es = LENGTH ces` assume_tac >>
  fsrw_tac[boolSimps.DNF_ss][MEM_ZIP] >>
  first_x_assum (assume_tac o (CONV_RULE (RESORT_FORALL_CONV (fn [n,cenv,res,cw] => [cenv,cw,n,res] | _ => raise mk_HOL_ERR"""""")))) >>
  pop_assum (qspecl_then [`cenv`,`cw`] mp_tac) >> rw[] >>
  fs[GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM] >>
  fs[evaluate_con,Cevaluate_con] >>
  Cases_on `do_con_check cenv cn (LENGTH Ces)` >> fs[] >> rw[] >- (
    fs[evaluate_list_with_evaluate,evaluate_list_with_error,Cevaluate_list_with_Cevaluate,Cevaluate_list_with_error] >>
    qexists_tac `f n (Rerr err)` >> rw[] >>
    first_assum (qspecl_then [`n`,`Rerr err`] mp_tac) >>
    Cases_on `f n (Rerr err)` >> rw[Cevaluate_list_with_error] >>
    qexists_tac `n` >> rw[] >>
    res_tac >>
    first_x_assum (qspecl_then [`m`,`Rval v`] mp_tac) >>
    `m < LENGTH Ces` by srw_tac[ARITH_ss][] >>
    rw[] >>
    Cases_on `f m (Rval v)` >> fs[] >>
    metis_tac[] )
  >- (
    fs[evaluate_list_with_evaluate,Cevaluate_list_with_Cevaluate] >>
    fs[evaluate_list_with_value,Cevaluate_list_with_value] >>
    qexists_tac `Rval (CConv (cm ' cn) (GENLIST (λn. @v. (f n (Rval (EL n vs))) = Rval v) (LENGTH vs)))` >>
    rw[] >- (
      first_x_assum (qspec_then `n` mp_tac) >>
      first_x_assum (qspec_then `n` mp_tac) >>
      rw[] >>
      first_x_assum (qspec_then `Rval (EL n vs)` mp_tac) >>
      Cases_on `f n (Rval (EL n vs))` >> rw[] )
    >- (
      fs[good_cmaps_def,good_cm_cw_def] ) >>
    rw[MAP_EQ_EVERY2,EVERY2_EVERY,EVERY_MEM,MEM_ZIP,pairTheory.FORALL_PROD] >>
    rw[EL_GENLIST] >>
    first_x_assum (qspec_then `n` mp_tac) >>
    first_x_assum (qspec_then `n` mp_tac) >>
    rw[] >>
    first_x_assum (qspec_then `Rval (EL n vs)` mp_tac) >>
    Cases_on `f n (Rval (EL n vs))` >> rw[] ) >>
  qexists_tac `Rerr Rtype_error` >> rw[] >>
  need Cevaluate to do a con check?
  ) >>
fs[evaluate_var] >> fs[] >> rw[] >>
fs[good_G_def,good_cmaps_def] >>
first_x_assum (match_mp_tac o GSYM) >>
metis_tac[])
*)

val FOLDR_CONS_triple = store_thm(
"FOLDR_CONS_triple",
``!f ls a. FOLDR (\(x,y,z) w. f x y z :: w) a ls = (MAP (\(x,y,z). f x y z) ls)++a``,
GEN_TAC THEN
Induct THEN1 SRW_TAC[][] THEN
Q.X_GEN_TAC `p` THEN
PairCases_on `p` THEN
SRW_TAC[][])

(* TODO: move? *)
val FOLDR_invariant = store_thm(
"FOLDR_invariant",
``∀P ls f a. P a ∧ (∀x a. MEM x ls ∧ P a ⇒ P (f x a)) ⇒ P (FOLDR f a ls)``,
GEN_TAC THEN Induct THEN SRW_TAC[][])

(* TODO: move *)
val cond_sum_expand = store_thm(
"cond_sum_expand",
``(!x y z. ((if P then INR x else INL y) = INR z) = (P /\ (z = x))) /\
  (!x y z. ((if P then INR x else INL y) = INL z) = (~P /\ (z = y))) /\
  (!x y z. ((if P then INL x else INR y) = INL z) = (P /\ (z = x))) /\
  (!x y z. ((if P then INL x else INR y) = INR z) = (~P /\ (z = y)))``,
Cases_on `P` >> fs[] >> rw[EQ_IMP_THM])

val exp_to_Cexp_nice_ind = save_thm(
"exp_to_Cexp_nice_ind",
exp_to_Cexp_ind
|> Q.SPECL [`P`
   ,`λs defs. EVERY (λ(d,vn,e). P s e) defs`
   ,`λs pes. EVERY (λ(p,e). P s e) pes`
   ,`λs. EVERY (P s)`]
|> SIMP_RULE (srw_ss()) []
|> UNDISCH_ALL
|> CONJUNCTS
|> el 1
|> DISCH_ALL
|> Q.GEN `P`
|> SIMP_RULE (srw_ss()) [optionTheory.option_case_compute,cond_sum_expand])

val exps_to_Cexps_MAP = store_thm(
"exps_to_Cexps_MAP",
``∀s es. exps_to_Cexps s es = MAP (exp_to_Cexp s) es``,
gen_tac >> Induct >> rw[exp_to_Cexp_def])

val pes_to_Cpes_MAP = store_thm(
"pes_to_Cpes_MAP",
``∀s pes. pes_to_Cpes s pes = MAP (λ(p,e). let (pvs,Cp) = pat_to_Cpat s [] p in (Cp, exp_to_Cexp s e)) pes``,
gen_tac >> Induct >- rw[exp_to_Cexp_def] >>
Cases >> rw[exp_to_Cexp_def])

val defs_to_Cdefs_MAP = store_thm(
"defs_to_Cdefs_MAP",
``∀s defs. defs_to_Cdefs s defs = (MAP FST defs, MAP (λ(d,vn,e). ([vn],exp_to_Cexp s e)) defs)``,
gen_tac >> Induct >- rw[exp_to_Cexp_def] >>
qx_gen_tac `d` >> PairCases_on `d` >> rw[exp_to_Cexp_def])

val vs_to_Cvs_MAP = store_thm(
"vs_to_Cvs_MAP",
``∀s vs. vs_to_Cvs s vs = MAP (v_to_Cv s) vs``,
gen_tac >> Induct >> rw[v_to_Cv_def])

val env_to_Cenv_MAP = store_thm(
"env_to_Cenv_MAP",
``∀s env. env_to_Cenv s env = MAP (λ(x,v). (x, v_to_Cv s v)) env``,
gen_tac >> Induct >- rw[exp_to_Cexp_def,v_to_Cv_def] >>
Cases >> rw[exp_to_Cexp_def,v_to_Cv_def])

val pat_to_Cpat_empty_pvs = store_thm(
"pat_to_Cpat_empty_pvs",
``(∀p m pvs. pat_to_Cpat m pvs p = (FST (pat_to_Cpat m [] p) ++ pvs, SND (pat_to_Cpat m [] p))) ∧
  (∀ps m pvs. pats_to_Cpats m pvs ps = ((FLAT (MAP (FST o pat_to_Cpat m []) ps))++pvs, MAP (SND o pat_to_Cpat m []) ps))``,
ho_match_mp_tac (TypeBase.induction_of``:pat``) >>
strip_tac >- rw[pat_to_Cpat_def] >>
strip_tac >- rw[pat_to_Cpat_def] >>
strip_tac >- rw[pat_to_Cpat_def] >>
strip_tac >- rw[pat_to_Cpat_def] >>
Cases
>- rw[pat_to_Cpat_def]
>- rw[pat_to_Cpat_def] >>
rpt strip_tac >>
simp_tac(srw_ss())[pat_to_Cpat_def,LET_THM] >>
qabbrev_tac `p = pats_to_Cpats m pvs ps` >>
PairCases_on `p` >> fs[] >>
qabbrev_tac `q = pats_to_Cpats m p0 l` >>
PairCases_on `q` >> fs[] >>
qabbrev_tac `r = pats_to_Cpats m [] l` >>
PairCases_on `r` >> fs[] >>
fs[pat_to_Cpat_def,LET_THM] >>
first_x_assum (qspecl_then [`m`,`pvs`] mp_tac) >>
rpt (pop_assum (mp_tac o SYM o SIMP_RULE(srw_ss())[markerTheory.Abbrev_def])) >>
simp_tac(srw_ss())[] >> rpt (disch_then assume_tac) >>
first_assum (qspecl_then [`m`,`p0`] mp_tac) >>
qpat_assum `X = (q0,q1)` mp_tac >>
qpat_assum `X = (r0,r1)` mp_tac >>
simp_tac(srw_ss())[] >> rw[])

val Cevaluate_FUPDATE = store_thm(
"Cevaluate_FUPDATE",
``∀env exp res k v. Cevaluate env exp res ∧
 (free_vars exp ⊆ FDOM env) ∧
 k ∉ free_vars exp
 ⇒ ∃res'. Cevaluate (env |+ (k,v)) exp res' ∧ result_rel syneq res res'``,
rw[] >>
qsuff_tac `env |+ (k,v) = (DRESTRICT env (free_vars exp)) ⊌ (env |+ (k,v))`
  >- metis_tac[Cevaluate_any_env,fmap_rel_refl,syneq_refl] >>
rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
rw[SUBMAP_DEF,FUNION_DEF,FUN_FMAP_DEF,DRESTRICT_DEF,FAPPLY_FUPDATE_THM] >>
fs[SUBSET_DEF] >> rw[] >> fs[])

val Cevaluate_super_env = store_thm(
"Cevaluate_super_env",
``∀s env exp res. Cevaluate (DRESTRICT env (free_vars exp)) exp res ∧ free_vars exp ⊆ s ∧ free_vars exp ⊆ FDOM env
  ⇒ ∃res'. Cevaluate (DRESTRICT env s) exp res' ∧ result_rel syneq res res'``,
rw[] >>
imp_res_tac Cevaluate_any_env >>
qpat_assum `free_vars exp ⊆ FDOM env` assume_tac >>
fs[DRESTRICT_DEF] >>
first_x_assum (qspec_then `DRESTRICT env (free_vars exp)` mp_tac) >>
rw[] >>
qmatch_abbrev_tac `∃res'. Cevaluate env1 exp res' ∧ result_rel syneq res res'` >>
first_x_assum (qspec_then `env1` strip_assume_tac) >>
qmatch_assum_abbrev_tac `Cevaluate (env0 ⊌ env1) exp res'` >>
qsuff_tac `env1 = env0 ⊌ env1` >- metis_tac[] >>
rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
fsrw_tac[][Abbr`env0`,Abbr`env1`,SUBMAP_DEF,SUBSET_DEF,DRESTRICT_DEF] >> rw[])

(* Prove compiler phases preserve semantics *)

(* TODO: move? *)
val ALOOKUP_NONE = store_thm(
"ALOOKUP_NONE",
``!l x. (ALOOKUP l x = NONE) = ~MEM x (MAP FST l)``,
SRW_TAC[][ALOOKUP_FAILS,MEM_MAP,pairTheory.FORALL_PROD])

(* TODO: move *)
val dest_var_def = save_thm("dest_var_def",CompileTheory.dest_var_def)
val _ = export_rewrites["dest_var_def"]

val dest_var_case = store_thm(
"dest_var_case",
``(dest_var e = SOME x) ⇒ (∃v. e = Var v)``,
Cases_on `e` >> rw[dest_var_def])

(*
val exp_to_Cexp_App_case = store_thm(
"exp_to_Cexp_App_case",
``(exp_to_Cexp s (App op e1 e2) = x) ⇒
  ((∃Ce Ces. (x = CCall Ce Ces) ∧ (op = Opapp)) ∨
   (∃ns es b. (x = CLet ns es b) ∧ ((op = Opb Gt) ∨ (op = Opb Geq))) ∨
   (∃Cop2 Ce1 Ce2. x = CPrim2 Cop2 Ce1 Ce2) ∨
   (∃Ce1 Ce2. x = CLprim CLeq [Ce1; Ce2]))``,
Cases_on `op` >> rw[exp_to_Cexp_def,LET_THM] >>
BasicProvers.EVERY_CASE_TAC >> rw[])

val exp_to_Cexp_cases = store_thm(
"exp_to_Cexp_cases",``
(¬(exp_to_Cexp s e = CDecl xs)) ∧
((exp_to_Cexp s e = CRaise err) = (e = Raise err)) ∧
((exp_to_Cexp s e = CVar n) = (∃x. (e = Var x) ∧ (n = s.vmap ' x))) ∧
((exp_to_Cexp s e = CVal Cv) = (∃v. (e = Val v) ∧ (Cv = v_to_Cv s v))) ∧
((exp_to_Cexp s e = CCon cn Ces) ⇒ (∃n es. (e = Con n es))) ∧
(¬(exp_to_Cexp s e = CTagEq Ce n)) ∧
(¬(exp_to_Cexp s e = CProj Ce n)) ∧
((exp_to_Cexp s e = CMat n Cpes) ⇒ (∃v pes. e = Mat (Var v) pes)) ∧
(¬(exp_to_Cexp s e = CLetfun F fns Cdefs Cb)) ∧
((exp_to_Cexp s e = CLet xs es Ce) ⇒ ((∃e1 pes. (e = Mat e1 pes) ∧ (dest_var e = NONE)) ∨ (∃opb e1 e2. (e = App (Opb opb) e1 e2) ∧ ((opb = Gt) ∨ (opb = Geq))) ∨ (∃x r b. e = Let x r b))) ∧
((exp_to_Cexp s e = CFun xs Ce) ⇒ (∃x b. e = Fun x b)) ∧
((exp_to_Cexp s e = CCall Ce es) ⇒ (∃e1 e2. e = App Opapp e1 e2)) ∧
((exp_to_Cexp s e = CLetfun T fns Cdefs Cb) ⇒ (∃defs b. e = Letrec defs b))``,
Cases_on `e` >> rw[exp_to_Cexp_def] >>
BasicProvers.EVERY_CASE_TAC >> rw[EQ_IMP_THM] >>
imp_res_tac dest_var_case >> fs[] >>
spose_not_then strip_assume_tac >>
imp_res_tac exp_to_Cexp_App_case >>
fs[LET_THM,pairTheory.UNCURRY] >> rw[])
*)

(* TODO: move? *)
val DIFF_SAME_UNION = store_thm(
"DIFF_SAME_UNION",
``!x y. ((x UNION y) DIFF x = y DIFF x) /\ ((x UNION y) DIFF y = x DIFF y)``,
SRW_TAC[][EXTENSION,EQ_IMP_THM])

val FOLDR_transitive_property = store_thm(
"FOLDR_transitive_property",
``!P ls f a. P [] a /\ (!n a. n < LENGTH ls /\ P (DROP (SUC n) ls) a ==> P (DROP n ls) (f (EL n ls) a)) ==> P ls (FOLDR f a ls)``,
GEN_TAC THEN Induct THEN SRW_TAC[][] THEN
`P ls (FOLDR f a ls)` by (
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SRW_TAC[][] THEN
  Q.MATCH_ASSUM_RENAME_TAC `P (DROP (SUC n) ls) b` [] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`SUC n`,`b`] MP_TAC) THEN
  SRW_TAC[][] ) THEN
FIRST_X_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN
SRW_TAC[][])

val MEM_DROP = store_thm(
"MEM_DROP",
``!x ls n. MEM x (DROP n ls) = (n < LENGTH ls /\ (x = (EL n ls))) \/ MEM x (DROP (SUC n) ls)``,
GEN_TAC THEN
Induct THEN1 SRW_TAC[][] THEN
NTAC 2 GEN_TAC THEN
SIMP_TAC (srw_ss()) [] THEN
Cases_on `n` THEN SIMP_TAC (srw_ss()) [] THEN
PROVE_TAC[])

val Cpat_vars_pat_to_Cpat = store_thm(
"Cpat_vars_pat_to_Cpat",
``(∀p s pvs pvs' Cp. (pat_to_Cpat s pvs p = (pvs',Cp))
  ⇒ (Cpat_vars Cp = pat_vars p)) ∧
  (∀ps s pvs pvs' Cps. (pats_to_Cpats s pvs ps = (pvs',Cps))
  ⇒ (MAP Cpat_vars Cps = MAP pat_vars ps))``,
ho_match_mp_tac (TypeBase.induction_of ``:pat``) >>
rw[pat_to_Cpat_def,LET_THM,pairTheory.UNCURRY] >>
rw[FOLDL_UNION_BIGUNION,IMAGE_BIGUNION] >- (
  qabbrev_tac `q = pats_to_Cpats s' pvs ps` >>
  PairCases_on `q` >>
  fsrw_tac[ETA_ss][MAP_EQ_EVERY2,EVERY2_EVERY,EVERY_MEM,pairTheory.FORALL_PROD] >>
  AP_TERM_TAC >>
  first_x_assum (qspecl_then [`s'`,`pvs`] mp_tac) >>
  rw[] >>
  pop_assum mp_tac >>
  rw[MEM_ZIP] >>
  rw[Once EXTENSION,MEM_EL] >>
  PROVE_TAC[] )
>- (
  qabbrev_tac `q = pats_to_Cpats s pvs ps` >>
  PairCases_on `q` >>
  qabbrev_tac `r = pat_to_Cpat s q0 p` >>
  PairCases_on `r` >>
  fs[] >>
  PROVE_TAC[] )
>- (
  fs[Once pat_to_Cpat_empty_pvs] ))

(* TODO: move? *)
val fresh_var_not_in = store_thm(
"fresh_var_not_in",
``∀s. (∃n. num_to_hex_string n ∉ s) ⇒ fresh_var s ∉ s``,
rw[CompileTheory.fresh_var_def] >>
numLib.LEAST_ELIM_TAC >> fs[] >>
PROVE_TAC[])

val FINITE_has_fresh_string = store_thm(
"FINITE_has_fresh_string",
``∀s. FINITE s ⇒ ∃n. num_to_hex_string n ∉ s``,
rw[] >>
qexists_tac `LEAST n. n ∉ IMAGE num_from_hex_string s` >>
numLib.LEAST_ELIM_TAC >>
conj_tac >- (
  PROVE_TAC[INFINITE_NUM_UNIV,IMAGE_FINITE,NOT_IN_FINITE] ) >>
rw[] >> pop_assum (qspec_then `num_to_hex_string n` mp_tac) >>
rw[SIMP_RULE(srw_ss())[FUN_EQ_THM]bitTheory.num_hex_string])

val NOT_fresh_var = store_thm(
"NOT_fresh_var",
``∀s x. x ∈ s ∧ FINITE s ⇒ x ≠ fresh_var s``,
PROVE_TAC[FINITE_has_fresh_string,fresh_var_not_in])

val free_vars_exp_to_Cexp = store_thm(
"free_vars_exp_to_Cexp",
``∀s e. free_vars (exp_to_Cexp s e) = FV e``,
ho_match_mp_tac exp_to_Cexp_nice_ind >>
srw_tac[ETA_ss,DNF_ss][exp_to_Cexp_def,exps_to_Cexps_MAP,pes_to_Cpes_MAP,defs_to_Cdefs_MAP,
FOLDL_UNION_BIGUNION,IMAGE_BIGUNION,BIGUNION_SUBSET,LET_THM,EVERY_MEM] >>
rw[] >- (
  AP_TERM_TAC >>
  rw[Once EXTENSION] >>
  fsrw_tac[DNF_ss][MEM_MAP,EVERY_MEM] >>
  PROVE_TAC[] )
>- (
  fs[] >>
  BasicProvers.EVERY_CASE_TAC >> rw[] >>
  srw_tac[DNF_ss][Once EXTENSION] >>
  PROVE_TAC[] )
>- (
  srw_tac[DNF_ss][Once EXTENSION] >>
  PROVE_TAC[] )
>- (
  fs[EVERY_MEM,pairTheory.FORALL_PROD] >>
  Cases_on `dest_var e` >> fs[] >>
  rw[FOLDL_UNION_BIGUNION_paired,DIFF_SAME_UNION,UNION_COMM] >>
  imp_res_tac dest_var_case >> rw[] >> fs[] >> rw[] >>
  AP_TERM_TAC >>
  rw[Once EXTENSION,MEM_MAP,pairTheory.EXISTS_PROD] >>
  srw_tac[DNF_ss][] >>
  fs[SUBSET_DEF,pairTheory.UNCURRY] >>
  srw_tac[DNF_ss][CONJ_ASSOC, Once CONJ_COMM] >>
  ((qho_match_abbrev_tac `
      (∃p1 p2. A p1 p2 ∧ MEM (p1,p2) pes) =
      (∃p1 p2. B p1 p2 ∧ MEM (p1,p2) pes)`)
   ORELSE
   (rw[Once(GSYM CONJ_ASSOC),SimpLHS] >>
    qho_match_abbrev_tac `
      (∃p1 p2. MEM (p1,p2) pes ∧ A p1 p2) =
      (∃p1 p2. B p1 p2 ∧ MEM (p1,p2) pes)`)) >>
  (qsuff_tac `∀p1 p2. MEM (p1,p2) pes ⇒ (A p1 p2 = B p1 p2)` >- PROVE_TAC[]) >>
  srw_tac[DNF_ss][Abbr`A`,Abbr`B`] >>
  first_x_assum (qspecl_then [`p1`,`p2`] mp_tac) >>
  qabbrev_tac `q = pat_to_Cpat s [] p1` >>
  PairCases_on `q` >> fs[] >>
  fs[markerTheory.Abbrev_def] >>
  qpat_assum`X = pat_to_Cpat s [] p1` (assume_tac o SYM) >>
  imp_res_tac Cpat_vars_pat_to_Cpat >>
  strip_tac >> fs[] >>
  EQ_TAC >> strip_tac >> fs[] >>
  match_mp_tac NOT_fresh_var >>
  srw_tac[DNF_ss][pairTheory.EXISTS_PROD,MEM_MAP] >>
  PROVE_TAC[] )
>- (
  rw[EXTENSION] >> PROVE_TAC[] )
>- (
  fs[FOLDL_UNION_BIGUNION_paired] >>
  qmatch_abbrev_tac `X ∪ Y = Z ∪ A` >>
  `X = A` by (
    fs[markerTheory.Abbrev_def] >>
    rw[LIST_TO_SET_MAP] ) >>
  rw[UNION_COMM] >>
  unabbrev_all_tac >>
  ntac 2 AP_TERM_TAC >>
  rw[Once EXTENSION,pairTheory.EXISTS_PROD,LIST_TO_SET_MAP,DIFF_UNION,DIFF_COMM] >>
  srw_tac[DNF_ss][MEM_MAP,pairTheory.EXISTS_PROD,pairTheory.UNCURRY] >>
  fs[pairTheory.FORALL_PROD] >>
  PROVE_TAC[] )
>- (
  qabbrev_tac `q = pat_to_Cpat s [] p` >>
  PairCases_on`q`>>fs[] )
>- (
  qmatch_assum_rename_tac `MEM d defs`[] >>
  PairCases_on `d` >> fs[] >>
  qabbrev_tac `q = pat_to_Cpat s [] p` >>
  PairCases_on `q` >> fs[pairTheory.FORALL_PROD] >>
  PROVE_TAC[]))

(*
val v_to_Cv_inj_rwt = store_thm(
"v_to_Cv_inj_rwt",
``∀s v1 v2. (v_to_Cv s v1 = v_to_Cv s v2) = (v1 = v2)``,
probably not true until equality is corrected in the source language *)

val MAP_values_fmap_to_alist = store_thm(
"MAP_values_fmap_to_alist",
``∀f fm. MAP (λ(k,v). (k, f v)) (fmap_to_alist fm) = fmap_to_alist (f o_f fm)``,
rw[fmap_to_alist_def,MAP_MAP_o,MAP_EQ_f])

val alist_to_fmap_MAP_values = store_thm(
"alist_to_fmap_MAP_values",
``∀f al. alist_to_fmap (MAP (λ(k,v). (k, f v)) al) = f o_f (alist_to_fmap al)``,
rw[] >>
Q.ISPECL_THEN [`I:γ->γ`,`f`,`al`] match_mp_tac alist_to_fmap_MAP_matchable >>
rw[INJ_I])

(*
val exp_to_Cexp_thm1 = store_thm(
"exp_to_Cexp_thm1",
``(∀s exp cenv env res.
  evaluate cenv env exp res ∧
  (res ≠ Rerr Rtype_error) ∧
  clV_exp exp ⊆ FDOM s.vmap ∧
  FV exp ⊆ FDOM s.vmap ∧
  good_env_state env s ⇒
  ∀Cexp. (Cexp = exp_to_Cexp s exp) ⇒
    Cevaluate
     (force_dom (alist_to_fmap (MAP (λ(x,v). (s.vmap ' x, v_to_Cv s v)) env)) (free_vars Cexp) (CLit (Bool F)))
     Cexp
     (map_result (v_to_Cv s) res))
∧ (∀(s:repl_state) (v:v). T)``,
ho_match_mp_tac exp_to_Cexp_nice_ind >>
strip_tac >- rw[exp_to_Cexp_def] >>
strip_tac >- (
  rw[exp_to_Cexp_def] >>
  match_mp_tac EQ_SYM >>
  match_mp_tac (CONJUNCT2 ce_Cexp_canonical_id) >>
  match_mp_tac (CONJUNCT2 exp_to_Cexp_canonical) >>
  fs[good_env_state_def] ) >>
strip_tac >- (
  srw_tac[DNF_ss,ETA_ss][exp_to_Cexp_def,exps_to_Cexps_MAP,vs_to_Cvs_MAP,FOLDL_UNION_BIGUNION] >>
  fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL,SUBSET_DEF] >>
  fsrw_tac[]
    [evaluate_con,Cevaluate_con,
     evaluate_list_with_evaluate,Cevaluate_list_with_Cevaluate,
     evaluate_list_with_value,evaluate_list_with_error,
     Cevaluate_list_with_value,Cevaluate_list_with_error]
  >- (
    qexists_tac `n` >>
    `err ≠ Rtype_error` by (spose_not_then strip_assume_tac >> fs[]) >>
    fsrw_tac[SATISFY_ss][EL_MAP] >>
    conj_tac >- (
      first_x_assum (qspecl_then [`cenv`,`env`,`Rerr err`,`n`] mp_tac) >>
      fsrw_tac[DNF_ss,SATISFY_ss][SUBSET_DEF,MEM_MAP,MEM_EL,Cevaluate_super_env] ) >>
    qx_gen_tac `m` >> strip_tac >>
    first_x_assum (qspec_then `m` mp_tac) >> rw[] >>
    qexists_tac `v_to_Cv s v` >>
    first_x_assum (qspecl_then [`cenv`,`env`,`Rval v`,`m`] mp_tac) >>
    `m < LENGTH es` by srw_tac[ARITH_ss][] >>
    fsrw_tac[DNF_ss,SATISFY_ss][EL_MAP,SUBSET_DEF,MEM_MAP,MEM_EL,Cevaluate_super_env] )
  >- (
    fs[exp_to_Cexp_def,vs_to_Cvs_MAP,EL_MAP] >>
    qx_gen_tac `n` >> strip_tac >>
    first_x_assum (qspec_then `n` mp_tac) >> rw[] >>
    first_x_assum (qspecl_then [`cenv`,`env`,`Rval (EL n vs)`,`n`] mp_tac) >>
    fsrw_tac[DNF_ss,SATISFY_ss][EL_MAP,SUBSET_DEF,MEM_MAP,MEM_EL,Cevaluate_super_env] )) >>
strip_tac >- (
  rw[exp_to_Cexp_def,evaluate_var] >> rw[] >>
  qmatch_abbrev_tac `v_to_Cv s v = ce_Cv (force_dom (alist_to_fmap mal) u d ' x)` >>
  `INJ (FAPPLY s.vmap) (set (MAP FST env)) UNIV` by (
    fs[good_env_state_def,good_repl_state_def,LIST_TO_SET_MAP] >>
    PROVE_TAC[INJ_SUBSET,SUBSET_REFL] ) >>
  `alist_to_fmap mal = MAP_KEYS (FAPPLY s.vmap) ((v_to_Cv s) o_f alist_to_fmap env)` by (
    Q.ISPECL_THEN [`FAPPLY s.vmap`,`v_to_Cv s`,`env`] match_mp_tac alist_to_fmap_MAP_matchable >>
    rw[Abbr`mal`] ) >>
  unabbrev_all_tac >>
  imp_res_tac ALOOKUP_MEM >>
  reverse (rw[force_dom_DRESTRICT_FUNION,FUNION_DEF,DRESTRICT_DEF,MAP_KEYS_def,MEM_MAP,pairTheory.EXISTS_PROD,o_f_DEF]) >-
    PROVE_TAC[] >>
  qmatch_abbrev_tac `v_to_Cv s v = ce_Cv (MAP_KEYS f fm ' (f y))` >>
  `y ∈ FDOM fm` by (
    unabbrev_all_tac >>
    rw[MEM_MAP,pairTheory.EXISTS_PROD] >>
    PROVE_TAC[] ) >>
  rw[MAP_KEYS_def,Abbr`fm`] >>
  rw[o_f_DEF] >>
  imp_res_tac ALOOKUP_SOME_FAPPLY_alist_to_fmap >>
  fs[] >>
  match_mp_tac EQ_SYM >>
  match_mp_tac (CONJUNCT2 ce_Cexp_canonical_id) >>
  match_mp_tac (CONJUNCT2 exp_to_Cexp_canonical) >>
  fsrw_tac[DNF_ss][good_env_state_def,SUBSET_DEF,pairTheory.FORALL_PROD] >>
  PROVE_TAC[] ) >>
strip_tac >- (
  rw[exp_to_Cexp_def,env_to_Cenv_MAP] >>
  rw[Cevaluate_fun] >>
  rw[mk_env_def] >>
  unabbrev_all_tac >>
  rw[MAP_values_fmap_to_alist,o_f_force_dom,alist_to_fmap_MAP_values] ) >>
strip_tac >- (
  rw[exp_to_Cexp_def,evaluate_app]
  >- (
    rw[Once Cevaluate_cases] >>
    disj1_tac >>
    rw[Cevaluate_list_with_Cevaluate,Cevaluate_list_with_EVERY] >>
    qexists_tac `v_to_Cv s v1` >>
    qexists_tac `v_to_Cv s v2` >>
    first_x_assum (qspecl_then [`cenv`,`env`,`Rval v1`] mp_tac) >>
    first_x_assum (qspecl_then [`cenv`,`env`,`Rval v2`] mp_tac) >>
    fs[Cevaluate_super_env] >> ntac 2 strip_tac >>
    qmatch_assum_rename_tac `do_app env (Opn opn) v1 v2 = SOME (env',exp'')` [] >>
    Cases_on `opn` >>
    Cases_on `v1` >> Cases_on `l` >> fs[MiniMLTheory.do_app_def] >>
    Cases_on `v2` >> Cases_on `l` >> fs[] >> rw[] >>
    fs[CevalPrim2_def,doPrim2_def,exp_to_Cexp_def,MiniMLTheory.opn_lookup_def,i0_def] >>
    rw[] >> fs[] >> rw[] >> fs[] >>
    rw[exp_to_Cexp_def] )
  >- (
    rw[Once Cevaluate_cases] >>
    disj2_tac >>
    rw[Cevaluate_list_with_Cevaluate,Cevaluate_list_with_error] >>
    qexists_tac `1` >>
    first_x_assum (qspecl_then [`cenv`,`env`,`Rval v1`] mp_tac) >>
    first_x_assum (qspecl_then [`cenv`,`env`,`Rerr err`] mp_tac) >>
    fs[Cevaluate_super_env] >> ntac 2 strip_tac >>
    Cases >> srw_tac[ARITH_ss][] >>
    qexists_tac `v_to_Cv s v1` >>
    fs[Cevaluate_super_env] )
  >- (
    rw[Once Cevaluate_cases] >>
    disj2_tac >>
    rw[Cevaluate_list_with_Cevaluate,Cevaluate_list_with_error] >>
    qexists_tac `0` >>
    first_x_assum (qspecl_then [`cenv`,`env`,`Rerr err`] mp_tac) >>
    fs[Cevaluate_super_env] )) >>
strip_tac >- (
  rw[exp_to_Cexp_def,evaluate_app]
  >- (
    first_x_assum (qspecl_then [`cenv`,`env`,`Rval v1`] mp_tac) >>
    first_x_assum (qspecl_then [`cenv`,`env`,`Rval v2`] mp_tac) >>
    fs[] >> ntac 2 strip_tac >>
    Cases_on `(opb = Lt) ∨ (opb = Leq)` >- (
      fs[] >>
      rw[Once Cevaluate_cases] >>
      disj1_tac >>
      rw[Cevaluate_list_with_Cevaluate,Cevaluate_list_with_EVERY] >>
      qexists_tac `v_to_Cv s v1` >>
      qexists_tac `v_to_Cv s v2` >>
      fs[Cevaluate_super_env] >>
      Cases_on `v1` >> Cases_on `l` >> fs[MiniMLTheory.do_app_def] >>
      Cases_on `v2` >> Cases_on `l` >> fs[] >> rw[] >>
      fs[CevalPrim2_def,doPrim2_def,exp_to_Cexp_def,MiniMLTheory.opb_lookup_def,i0_def] )
    >- (
      Cases_on `opb` >> fs[] >>
      rw[Once Cevaluate_cases] >>
      disj1_tac >>
      qexists_tac `v_to_Cv s v1` >>
      fsrw_tac[SATISFY_ss][GSYM INSERT_SING_UNION,Cevaluate_super_env] >>
      rw[Once Cevaluate_cases] >>
      disj1_tac >>
      qexists_tac `v_to_Cv s v2` >> (
      conj_tac >- (
        match_mp_tac Cevaluate_FUPDATE >>
        fs[good_env_state_def] >>
        fs[free_vars_exp_to_Cexp,Abbr`Ce1`,Abbr`Ce2`] >>
        reverse conj_tac >- (
          fs[good_repl_state_def,FRANGE_DEF,SUBSET_DEF] >>
          metis_tac[prim_recTheory.LESS_REFL] ) >>
        fsrw_tac[SATISFY_ss][Cevaluate_super_env,free_vars_exp_to_Cexp] )) >>
      rw[Once Cevaluate_cases] >>
      disj1_tac >>
      rw[Cevaluate_list_with_Cevaluate] >>
      rw[Cevaluate_list_with_cons] >>
      srw_tac[ARITH_ss][FAPPLY_FUPDATE_THM] >>
      Cases_on `v1` >> Cases_on `l` >> fs[MiniMLTheory.do_app_def] >>
      Cases_on `v2` >> Cases_on `l` >> fs[] >> rw[] >>
      fs[doPrim2_def,exp_to_Cexp_def,MiniMLTheory.opb_lookup_def] >>
      rw[integerTheory.int_gt,integerTheory.int_ge] ))
  >- (
    Cases_on `(opb = Lt) ∨ (opb = Leq)` >- (
      fs[] >>
      rw[Once Cevaluate_cases] >>
      disj2_tac >>
      rw[Cevaluate_list_with_Cevaluate,Cevaluate_list_with_cons] >>
      disj1_tac >>
      qexists_tac `v_to_Cv s v1` >>
      first_x_assum (qspecl_then [`cenv`,`env`,`Rval v1`] mp_tac) >>
      first_x_assum (qspecl_then [`cenv`,`env`,`Rerr err`] mp_tac) >>
      fs[Cevaluate_super_env] )
    >- (
      Cases_on `opb` >> fs[] >>
      rw[Once Cevaluate_cases] >>
      disj1_tac >>
      qexists_tac `v_to_Cv s v1` >>
      first_x_assum (qspecl_then [`cenv`,`env`,`Rval v1`] mp_tac) >>
      fsrw_tac[SATISFY_ss][GSYM INSERT_SING_UNION,Cevaluate_super_env] >>
      strip_tac >>
      rw[Once Cevaluate_cases] >>
      disj2_tac >>
      match_mp_tac Cevaluate_FUPDATE >>
      first_x_assum (qspecl_then [`cenv`,`env`,`Rerr err`] mp_tac) >>
      fs[good_env_state_def] >>
      fs[free_vars_exp_to_Cexp,Abbr`Ce1`,Abbr`Ce2`] >>
      strip_tac >> (
      reverse conj_tac >- (
        fs[good_repl_state_def,FRANGE_DEF,SUBSET_DEF] >>
        metis_tac[prim_recTheory.LESS_REFL] )) >>
      fsrw_tac[SATISFY_ss][Cevaluate_super_env,free_vars_exp_to_Cexp] ))
  >- (
    Cases_on `(opb = Lt) ∨ (opb = Leq)` >- (
      fs[] >>
      rw[Once Cevaluate_cases] >>
      disj2_tac >>
      rw[Cevaluate_list_with_Cevaluate,Cevaluate_list_with_cons] >>
      disj2_tac >>
      first_x_assum (qspecl_then [`cenv`,`env`,`Rerr err`] mp_tac) >>
      fs[Cevaluate_super_env] )
    >- (
      Cases_on `opb` >> fs[] >>
      rw[Once Cevaluate_cases] >>
      disj2_tac >>
      first_x_assum (qspecl_then [`cenv`,`env`,`Rerr err`] mp_tac) >>
      fsrw_tac[SATISFY_ss][GSYM INSERT_SING_UNION,Cevaluate_super_env]  ))) >>
strip_tac >- (
  rw[exp_to_Cexp_def,evaluate_app]
  >- (
    rw[Once Cevaluate_cases] >>
    disj1_tac >>
    rw[Cevaluate_list_with_Cevaluate,Cevaluate_list_with_EVERY] >>
    qexists_tac `v_to_Cv s v1` >>
    qexists_tac `v_to_Cv s v2` >>
    first_x_assum (qspecl_then [`cenv`,`env`,`Rval v1`] mp_tac) >>
    first_x_assum (qspecl_then [`cenv`,`env`,`Rval v2`] mp_tac) >>
    fs[Cevaluate_super_env] >> ntac 2 strip_tac >>
    fs[MiniMLTheory.do_app_def] >> rw[] >>
    fs[evaluate_val] >> rw[exp_to_Cexp_def] >>
    sorry )
  >- (
    rw[Once Cevaluate_cases] >>
    rw[Cevaluate_list_with_Cevaluate,Cevaluate_list_with_error] >>
    qexists_tac `1` >>
    first_x_assum (qspecl_then [`cenv`,`env`,`Rval v1`] mp_tac) >>
    first_x_assum (qspecl_then [`cenv`,`env`,`Rerr err`] mp_tac) >>
    fs[Cevaluate_super_env] >> ntac 2 strip_tac >>
    Cases >> srw_tac[ARITH_ss][] >>
    qexists_tac `v_to_Cv s v1` >>
    fs[Cevaluate_super_env] )
  >- (
    rw[Once Cevaluate_cases] >>
    rw[Cevaluate_list_with_Cevaluate,Cevaluate_list_with_error] >>
    qexists_tac `0` >>
    first_x_assum (qspecl_then [`cenv`,`env`,`Rerr err`] mp_tac) >>
    fs[Cevaluate_super_env] )) >>
strip_tac >- (
  rw[exp_to_Cexp_def,evaluate_app]
  >- (
    fs[MiniMLTheory.do_app_def] >>
    Cases_on `v1` >> fs[] >> rw[]
    >- (
      rw[Once Cevaluate_cases] >>
      disj1_tac >>
      qmatch_assum_rename_tac `evaluate cenv env exp (Rval (Closure env' v b))`[] >>
      first_x_assum (qspecl_then [`cenv`,`env`,`Rval (Closure env' v b)`] mp_tac) >>
      fs[exp_to_Cexp_def,LET_THM] >>
      qabbrev_tac`p = extend s v` >>
      PairCases_on`p` >> fs[] >>
      fs[exp_to_Cexp_def] >> rw[] >>
      qmatch_assum_abbrev_tac `Cevaluate Cenv Ce1 (Rval (CClosure Cenv' ns Cb))` >>
      map_every qexists_tac [`Cenv'`,`ns`,`Cb`] >>
      fs[Cevaluate_super_env,Abbr`Cenv`] >>
      srw_tac[DNF_ss][Cevaluate_list_with_Cevaluate,Cevaluate_list_with_cons,Abbr`ns`] >>
      qexists_tac `v_to_Cv s v2` >>
      first_x_assum (qspecl_then [`cenv`,`env`,`Rval v2`] mp_tac) >>
      fs[Cevaluate_super_env] >> strip_tac >>

*)

val tacLt =
  rw[Once Cevaluate_cases] >>
  disj1_tac >>
  rw[Cevaluate_list_with_Cevaluate] >>
  rw[Cevaluate_list_with_cons] >>
  qexists_tac `v_to_Cv s v1` >>
  qexists_tac `v_to_Cv s v2` >>
  rw[] >>
  Cases_on `v1` >> Cases_on `l` >> fs[MiniMLTheory.do_app_def] >>
  Cases_on `v2` >> Cases_on `l` >> fs[] >> rw[] >>
  fs[CevalPrim2_def,doPrim2_def,exp_to_Cexp_def,MiniMLTheory.opb_lookup_def] >>
  fsrw_tac[SATISFY_ss][Cevaluate_super_env]

val tacGt =
  rw[Once Cevaluate_cases] >>
  disj1_tac >>
  qexists_tac `v_to_Cv m v1` >>
  fsrw_tac[SATISFY_ss][GSYM INSERT_SING_UNION,Cevaluate_super_env] >>
  rw[Once Cevaluate_cases] >>
  disj1_tac >>
  qexists_tac `v_to_Cv m v2` >>
  conj_tac >- (
    match_mp_tac Cevaluate_FUPDATE >>
    fs[] >>
    fs[free_vars_exp_to_Cexp] >>
    reverse conj_tac >- (
      unabbrev_all_tac >>
      match_mp_tac fresh_var_not_in >>
      match_mp_tac FINITE_has_fresh_string >>
      rw[]) >>
    fsrw_tac[SATISFY_ss][Cevaluate_super_env,free_vars_exp_to_Cexp] ) >>
  rw[Once Cevaluate_cases] >>
  disj1_tac >>
  rw[Cevaluate_list_with_Cevaluate] >>
  rw[Cevaluate_list_with_cons] >>
  `x1 ≠ x2` by (
    rw[Abbr`x1`,Abbr`x2`] >>
    match_mp_tac NOT_fresh_var >>
    rw[] ) >>
  srw_tac[ARITH_ss][FAPPLY_FUPDATE_THM] >>
  Cases_on `v1` >> Cases_on `l` >> fs[MiniMLTheory.do_app_def] >>
  Cases_on `v2` >> Cases_on `l` >> fs[] >> rw[] >>
  fs[doPrim2_def,exp_to_Cexp_def,MiniMLTheory.opb_lookup_def] >>
  rw[integerTheory.int_gt,integerTheory.int_ge]

(* TODO: Move *)
val alist_to_fmap_PERM = store_thm(
"alist_to_fmap_PERM",
``∀l1 l2. PERM l1 l2 ∧ ALL_DISTINCT (MAP FST l1) ⇒ (alist_to_fmap l1 = alist_to_fmap l2)``,
let open sortingTheory in
qsuff_tac
  `∀l1 l2. PERM l1 l2 ⇒ ALL_DISTINCT (MAP FST l1) ⇒ PERM l1 l2 ∧ (alist_to_fmap l1 = alist_to_fmap l2)`
  >- rw[] >>
ho_match_mp_tac PERM_IND >>
fs[pairTheory.FORALL_PROD] >>
rw[] >> fs[] >- (
  fs[PERM_SWAP_AT_FRONT] )
>- (
  match_mp_tac FUPDATE_COMMUTES >> rw[] )
>- (
  PROVE_TAC[PERM_TRANS,ALL_DISTINCT_PERM,PERM_MAP] )
>- (
  PROVE_TAC[PERM_TRANS,ALL_DISTINCT_PERM,PERM_MAP] )
end)

val exp_to_Cexp_thm1 = store_thm(
"exp_to_Cexp_thm1",
``∀cenv env exp res. evaluate cenv env exp res ⇒
  (res ≠ Rerr Rtype_error) ⇒
  ∀m. ∃Cres. Cevaluate (alist_to_fmap (env_to_Cenv m env)) (exp_to_Cexp m exp) Cres ∧
             result_rel syneq (map_result (v_to_Cv m) res) Cres``,
ho_match_mp_tac evaluate_nice_strongind >>
strip_tac >- rw[exp_to_Cexp_def,v_to_Cv_def] >>
strip_tac >- rw[exp_to_Cexp_def] >>
strip_tac >- (
  rw[exp_to_Cexp_def,v_to_Cv_def,
     exps_to_Cexps_MAP,vs_to_Cvs_MAP,
     evaluate_list_with_value,Cevaluate_con,
     Cevaluate_list_with_Cevaluate,Cevaluate_list_with_EVERY] >>
  rw[syneq_cases] >>
  fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,pairTheory.FORALL_PROD] >>
  first_x_assum (qspec_then `m` strip_assume_tac o CONV_RULE SWAP_FORALL_CONV) >>
  fs[Once (GSYM RIGHT_EXISTS_IMP_THM),SKOLEM_THM] >>
  qexists_tac `GENLIST f (LENGTH vs)` >>
  fsrw_tac[DNF_ss][MEM_ZIP,EL_MAP,EL_GENLIST,MAP_GENLIST,EL_MAP] ) >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[exp_to_Cexp_def,v_to_Cv_def,
     exps_to_Cexps_MAP,
     evaluate_list_with_error,Cevaluate_con,
     Cevaluate_list_with_Cevaluate,Cevaluate_list_with_error] >>
  fs[] >>
  first_x_assum (qspec_then `m` strip_assume_tac) >>
  qmatch_assum_rename_tac `Cevaluate Cenv (exp_to_Cexp m (EL k es)) (Rerr err)`["Cenv"] >>
  qexists_tac `k` >> fs[EL_MAP] >>
  qx_gen_tac `z` >> strip_tac >>
  first_x_assum (qspec_then `z` mp_tac) >> rw[] >>
  first_x_assum (qspec_then `m` strip_assume_tac) >>
  fsrw_tac[ARITH_ss][EL_MAP] >>
  PROVE_TAC[] ) >>
strip_tac >- (
  fs[exp_to_Cexp_def,MEM_MAP,pairTheory.EXISTS_PROD,env_to_Cenv_MAP] >>
  rpt gen_tac >> strip_tac >> qx_gen_tac `m` >>
  conj_asm1_tac >- PROVE_TAC [ALOOKUP_MEM] >>
  rw[alist_to_fmap_MAP_values] >>
  `n ∈ FDOM (alist_to_fmap env)` by (
    rw[MEM_MAP,pairTheory.EXISTS_PROD] >> PROVE_TAC[] ) >>
  rw[o_f_FAPPLY] >>
  PROVE_TAC[ALOOKUP_SOME_FAPPLY_alist_to_fmap,syneq_refl] ) >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[exp_to_Cexp_def,v_to_Cv_def,env_to_Cenv_MAP] >>
  rw[syneq_cases] >>
  srw_tac[DNF_ss][Abbr`Cenv`,ALOOKUP_MAP,FLOOKUP_DEF,optionTheory.OPTREL_def] >>
  Cases_on `ALOOKUP env v` >> fs[] ) >>
cheat)
(*
strip_tac >- (
  ntac 2 gen_tac >>
  Cases >> fs[exp_to_Cexp_def] >>
  qx_gen_tac `e1` >>
  qx_gen_tac `e2` >>
  rw[] >- (
    rw[Once Cevaluate_cases] >>
    disj1_tac >>
    rw[Cevaluate_list_with_Cevaluate] >>
    rw[Cevaluate_list_with_cons] >>
    qexists_tac `v_to_Cv m v1` >>
    qexists_tac `v_to_Cv m v2` >>
    fsrw_tac[][Cevaluate_super_env,Abbr`Ce1`,Abbr`Ce2`] >>
    qmatch_assum_rename_tac `do_app env (Opn opn) v1 v2 = SOME (env',exp'')` [] >>
    Cases_on `opn` >>
    Cases_on `v1` >> Cases_on `l` >> fs[MiniMLTheory.do_app_def] >>
    Cases_on `v2` >> Cases_on `l` >> fs[] >> rw[] >>
    fs[CevalPrim2_def,doPrim2_def,exp_to_Cexp_def,MiniMLTheory.opn_lookup_def,i0_def] >>
    rw[] >> fs[] >> rw[] >> fs[] >>
    rw[Once MiniMLTheory.evaluate_cases,exp_to_Cexp_def] )
  >- (
    qmatch_assum_rename_tac `do_app env (Opb opb) v1 v2 = SOME (env',exp'')` [] >>
    Cases_on `opb` >> fs[Abbr`Ce1`,Abbr`Ce2`]
    >- tacLt >- tacGt >- tacLt >- tacGt )
  >- (
    rw[Once Cevaluate_cases] >>
    disj1_tac >>
    rw[Cevaluate_list_with_Cevaluate] >>
    rw[Cevaluate_list_with_cons] >>
    qexists_tac `v_to_Cv m v1` >>
    qexists_tac `v_to_Cv m v2` >>
    fsrw_tac[][Cevaluate_super_env,Abbr`Ce1`,Abbr`Ce2`] >>
    fs[MiniMLTheory.do_app_def] >> rw[] >> fs[exp_to_Cexp_def] >>
    sorry )
  >- (
    fs[MiniMLTheory.do_app_def] >>
    Cases_on `v1` >> fs[] >- (
      rw[Once Cevaluate_cases] >>
      disj1_tac >>
      srw_tac[DNF_ss][Cevaluate_list_with_Cevaluate,Cevaluate_list_with_cons] >>
      qmatch_assum_rename_tac `evaluate cenv env e1 (Rval (Closure env' v b))`[] >>
      qpat_assum `∀s''. Cevaluate A B (Rval (v_to_Cv s'' (Closure env' v b)))` (qspec_then `m` mp_tac) >>
      fs[exp_to_Cexp_def,LET_THM] >>
      qmatch_abbrev_tac `Cevaluate Cenv Ce1 (Rval (CClosure Cenv' ns Cb)) ⇒ X` >>
      strip_tac >> qunabbrev_tac `X` >>
      map_every qexists_tac [`Cenv'`,`ns`,`Cb`] >>
      fs[Cevaluate_super_env,Abbr`ns`] >>
      qexists_tac `v_to_Cv m v2` >>
      qpat_assum `∀s. Cevaluate A B (Rval (v_to_Cv s v2))` (qspec_then `m` mp_tac) >>
      fs[Cevaluate_super_env] >>
      fsrw_tac[ETA_ss][MiniMLTheory.bind_def,env_to_Cenv_MAP,alist_to_fmap_MAP_values] >>
      strip_tac >>
      first_x_assum (qspec_then `m` mp_tac) >>
      unabbrev_all_tac >>
      srw_tac[ETA_ss][mk_env_def,alist_to_fmap_MAP_values] >>
      rw[ce_Cexp_canonical_id,exp_to_Cexp_canonical] >>
      qmatch_abbrev_tac `Cevaluate ((alist_to_fmap (sort_Cenv ls)) |+ kv) ee rr` >>
      `PERM (sort_Cenv ls) ls ∧ ALL_DISTINCT (MAP FST (sort_Cenv ls))` by (
        rw[Abbr`ls`,sort_Cenv_def] >>
        PROVE_TAC[sortingTheory.QSORT_PERM,sortingTheory.PERM_SYM] ) >>
      imp_res_tac alist_to_fmap_PERM >> fs[] >>
      unabbrev_all_tac >> rw[] >>
      `ce_Cv o v_to_Cv m = v_to_Cv m` by (
        rw[FUN_EQ_THM,ce_Cexp_canonical_id,exp_to_Cexp_canonical] ) >>
      fs[] >>
      rw[] >> (ntac 3 (pop_assum kall_tac)) >>
      Cases_on `{v} ⊆ free_vars (exp_to_Cexp m b)` >- (
        rw[force_dom_FUPDATE] >>
        rw[Once INSERT_SING_UNION] >>
        fs[UNION_DIFF] ) >>
      fs[] >>
      fs[force_dom_of_FUPDATE] >>
      fs[GSYM DELETE_DEF,DELETE_NON_ELEMENT] >>
      match_mp_tac Cevaluate_FUPDATE >>
      fs[GSYM DELETE_DEF,DELETE_NON_ELEMENT] )
    >-
*)

(*
val remove_mat_thm1 = store_thm(
"remove_mat_thm1",
``∀env exp res. Cevaluate env exp res ⇒ Cevaluate env (remove_mat exp) res``,
ho_match_mp_tac Cevaluate_nice_ind >>
strip_tac >- rw[remove_mat_def] >>
strip_tac >- rw[remove_mat_def] >>
strip_tac >- rw[remove_mat_def] >>
strip_tac >- (
  rw[remove_mat_def,Cevaluate_con,EL_MAP,
     Cevaluate_list_with_Cevaluate,Cevaluate_list_with_value] ) >>
strip_tac >- (
  rw[remove_mat_def,Cevaluate_con,EL_MAP,
     Cevaluate_list_with_Cevaluate,Cevaluate_list_with_error] >>
  fsrw_tac[SATISFY_ss,ETA_ss][] >>
  metis_tac[EL_MAP,arithmeticTheory.LESS_TRANS]) >>
strip_tac >- (
  rw[remove_mat_def,Cevaluate_tageq] >>
  PROVE_TAC[] ) >>
strip_tac >- (
  rw[remove_mat_def,Cevaluate_tageq] ) >>
strip_tac >- (
  rw[remove_mat_def,Cevaluate_proj] >>
  PROVE_TAC[] ) >>
strip_tac >- (
  rw[remove_mat_def,Cevaluate_proj] ) >>
strip_tac >- (
  rw[remove_mat_def] ) >>
strip_tac >- (
  rw[remove_mat_def] >>
  rw[Once Cevaluate_cases] >>
*)


(*
let rec
v_to_ov cenv (Lit l) = OLit l
and
v_to_ov cenv (Conv cn vs) = OConv cn (List.map (v_to_ov cenv) vs)
and
v_to_ov cenv (Closure env vn e) = OFn
  (fun ov -> map_option (o (v_to_ov cenv) snd)
    (some (fun (a,r) -> v_to_ov cenv a = ov
           && evaluate cenv (bind vn a env) e (Rval r))))
and
v_to_ov cenv (Recclosure env defs n) = OFn
  (fun ov -> option_bind (optopt (find_recfun n defs))
    (fun (vn,e) -> map_option (o (v_to_ov cenv) snd)
      (some (fun (a,r) -> v_to_ov cenv a = ov
             && evaluate cenv (bind vn a (build_rec_env defs env)) e (Rval r)))))

let rec
Cv_to_ov m (CLit l) = OLit l
and
Cv_to_ov m (CConv cn vs) = OConv (Pmap.find cn m) (List.map (Cv_to_ov m) vs)
and
Cv_to_ov m (CClosure env ns e) = OFn
  (fun ov -> some
and
Cv_to_ov m (CRecClos env ns fns n) = OFn
*)

val _ = export_theory ()
