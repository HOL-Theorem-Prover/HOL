open HolKernel bossLib boolLib listTheory pred_setTheory finite_mapTheory alistTheory lcsymtacs
open SatisfySimps boolSimps compileTerminationTheory intLangTheory BytecodeTheory evaluateEquationsTheory

val _ = new_theory "compileCorrectness"

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
 (∀v. v ∈ FRANGE env ⇒ Cclosed v) ∧
 k ∉ free_vars exp ∧ Cclosed v
 ⇒ ∃res'. Cevaluate (env |+ (k,v)) exp res' ∧ result_rel syneq res res'``,
rw[] >>
`∀w. w ∈ FRANGE (env |+ (k,v)) ⇒ Cclosed w` by (
  fsrw_tac[DNF_ss][FRANGE_DEF,DOMSUB_FAPPLY_THM] ) >>
qsuff_tac `(env |+ (k,v) = (DRESTRICT env (free_vars exp)) ⊌ (env |+ (k,v)))`
  >- metis_tac[Cevaluate_any_env,fmap_rel_refl,syneq_refl] >>
rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
rw[SUBMAP_DEF,FUNION_DEF,FUN_FMAP_DEF,DRESTRICT_DEF,FAPPLY_FUPDATE_THM] >>
fs[SUBSET_DEF] >> rw[] >> fs[])

val Cevaluate_super_env = store_thm(
"Cevaluate_super_env",
``∀s env exp res. Cevaluate (DRESTRICT env (free_vars exp)) exp res ∧ free_vars exp ⊆ s
  ∧ free_vars exp ⊆ FDOM env ∧ (∀v. v ∈ FRANGE (DRESTRICT env s) ⇒ Cclosed v)
  ⇒ ∃res'. Cevaluate (DRESTRICT env s) exp res' ∧ result_rel syneq res res'``,
rw[] >>
qmatch_assum_abbrev_tac `Cevaluate e1 exp res` >>
qspecl_then [`e1`,`exp`,`res`] mp_tac Cevaluate_any_env >> rw[] >>
`free_vars exp ⊆ FDOM e1` by ( fs[Abbr`e1`,DRESTRICT_DEF] ) >>
`∀v. v ∈ FRANGE e1 ⇒ Cclosed v` by (
  fsrw_tac[DNF_ss][Abbr`e1`,FRANGE_DEF,DRESTRICT_DEF,SUBSET_DEF] ) >>
fs[] >>
first_x_assum (qspec_then `e1` mp_tac) >> rw[] >>
first_x_assum (qspec_then `DRESTRICT env s` mp_tac) >>
fs[] >> rw[] >>
unabbrev_all_tac >>
qmatch_abbrev_tac `∃res'. Cevaluate env1 exp res' ∧ result_rel syneq res res'` >>
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

val Cpes_vars_thm = store_thm(
"Cpes_vars_thm",
``Cpes_vars Cpes = BIGUNION (IMAGE Cpat_vars (set (MAP FST Cpes))) ∪ BIGUNION (IMAGE free_vars (set (MAP SND Cpes)))``,
rw[Cpes_vars_def] >>
rw[Once (GSYM UNION_ASSOC)] >>
rw[FOLDL_UNION_BIGUNION_paired] >>
srw_tac[DNF_ss][Once EXTENSION,MEM_MAP,pairTheory.EXISTS_PROD] >>
PROVE_TAC[])

val FINITE_Cpat_vars = store_thm(
"FINITE_Cpat_vars",
``∀p. FINITE (Cpat_vars p)``,
ho_match_mp_tac Cpat_vars_ind >>
rw[FOLDL_UNION_BIGUNION] >>
PROVE_TAC[])
val _ = export_rewrites["FINITE_Cpat_vars"]

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
  BasicProvers.EVERY_CASE_TAC >> rw[] )
>- (
  fs[EVERY_MEM,pairTheory.FORALL_PROD,FOLDL_UNION_BIGUNION_paired,Cpes_vars_thm] >>
  fs[MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD] >>
  rw[DIFF_SAME_UNION,UNION_COMM] >>
  AP_TERM_TAC >>
  rw[Once EXTENSION,MEM_MAP,pairTheory.EXISTS_PROD] >>
  srw_tac[DNF_ss][] >>
  fs[SUBSET_DEF,pairTheory.UNCURRY] >>
  srw_tac[DNF_ss][CONJ_ASSOC, Once CONJ_COMM] >>
  qho_match_abbrev_tac `
    (∃p1 p2. A p1 p2 ∧ MEM (p1,p2) pes) =
    (∃p1 p2. B p1 p2 ∧ MEM (p1,p2) pes)` >>
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
val _ = export_rewrites["free_vars_exp_to_Cexp"];

(*
val v_to_Cv_inj_rwt = store_thm(
"v_to_Cv_inj_rwt",
``∀s v1 v2. (v_to_Cv s v1 = v_to_Cv s v2) = (v1 = v2)``,
probably not true until equality is corrected in the source language *)

val MAP_values_fmap_to_alist = store_thm(
"MAP_values_fmap_to_alist",
``∀f fm. MAP (λ(k,v). (k, f v)) (fmap_to_alist fm) = fmap_to_alist (f o_f fm)``,
rw[fmap_to_alist_def,MAP_MAP_o,MAP_EQ_f])

val alist_to_fmap_MAP_matchable = store_thm(
"alist_to_fmap_MAP_matchable",
``∀f1 f2 al mal v. INJ f1 (set (MAP FST al)) UNIV ∧
  (mal = MAP (λ(x,y). (f1 x,f2 y)) al) ∧
  (v = MAP_KEYS f1 (f2 o_f alist_to_fmap al)) ⇒
  (alist_to_fmap mal = v)``,
METIS_TAC[alist_to_fmap_MAP])

val alist_to_fmap_MAP_values = store_thm(
"alist_to_fmap_MAP_values",
``∀f al. alist_to_fmap (MAP (λ(k,v). (k, f v)) al) = f o_f (alist_to_fmap al)``,
rw[] >>
Q.ISPECL_THEN [`I:γ->γ`,`f`,`al`] match_mp_tac alist_to_fmap_MAP_matchable >>
rw[INJ_I])

val v_to_Cv_closed = store_thm(
"v_to_Cv_closed",
``(∀m v. closed v ⇒ Cclosed (v_to_Cv m v)) ∧
  (∀m vs. EVERY closed vs ⇒ EVERY Cclosed (vs_to_Cvs m vs)) ∧
  (∀m env. EVERY closed (MAP SND env) ⇒ FEVERY (Cclosed o SND) (alist_to_fmap (env_to_Cenv m env)))``,
ho_match_mp_tac v_to_Cv_ind >>
rw[v_to_Cv_def] >> rw[Cclosed_rules]
>- (
  fs[Once closed_cases] >>
  rw[Cclosed_rules] )
>- (
  fs[Once closed_cases] >>
  rw[Once Cclosed_cases,Abbr`Ce`,Abbr`Cenv`,env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD,FST_pair] >>
  fs[SUBSET_DEF] >> PROVE_TAC[])
>- (
  fs[Once closed_cases] >>
  fs[defs_to_Cdefs_MAP] >> rw[] >>
  rw[Once Cclosed_cases,Abbr`Cenv`,env_to_Cenv_MAP] >>
  pop_assum mp_tac >> rw[EL_MAP] >>
  qabbrev_tac `p = EL i defs` >>
  PairCases_on `p` >> fs[] >> rw[] >>
  rw[MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD,FST_pair] >>
  fs[SUBSET_DEF] >> PROVE_TAC[] ) >>
first_x_assum (match_mp_tac o MP_CANON) >>
pop_assum mp_tac >>
rw[FRANGE_DEF,DOMSUB_FAPPLY_THM] >>
rw[] >> PROVE_TAC[])

val tacLt =
  rw[Once Cevaluate_cases] >>
  rw[Cevaluate_list_with_Cevaluate] >>
  rw[Cevaluate_list_with_cons] >>
  srw_tac[DNF_ss][] >>
  disj1_tac >>
  qexists_tac `w1` >>
  qexists_tac `w2` >>
  rw[] >>
  Cases_on `v1` >> Cases_on `l` >> fs[MiniMLTheory.do_app_def] >>
  Cases_on `v2` >> Cases_on `l` >> fs[] >> rw[] >>
  fs[CevalPrim2_def,doPrim2_def,exp_to_Cexp_def,MiniMLTheory.opb_lookup_def] >>
  rw[] >> fs[v_to_Cv_def] >> fs[Q.SPEC`CLitv l`syneq_cases]

(*
val tacGt =
  rw[Once Cevaluate_cases] >>
  srw_tac[DNF_ss][] >>
  disj1_tac >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `w1` >> fs[] >>
  rw[Once Cevaluate_cases] >>
  srw_tac[DNF_ss][] >>
  disj1_tac >>
  qmatch_assum_abbrev_tac `Cevaluate env0 exp0 (Rval w2)` >>
  `∀v. v ∈ FRANGE env0 ⇒ Cclosed v` by (
    imp_res_tac v_to_Cv_closed >>
    fs[FEVERY_DEF] >> PROVE_TAC[] ) >>
  `every_result Cclosed (Rval w1)` by (
    match_mp_tac (MP_CANON Cevaluate_closed)

  Q.ISPECL_THEN[`env0`,`exp0`,`Rval w2`,`fresh_var (free_vars exp0)`,`w1`]mp_tac Cevaluate_FUPDATE >>
  `∀v. v ∈ FRANGE env0 ⇒ Cclosed v` by (
    unabbrev_all_tac >>
    fsrw_tac[ETA_ss][env_to_Cenv_MAP,alist_to_fmap_MAP_values,o_f_FRANGE]

  fs[free_vars_exp_to_Cexp,Abbr`exp0`]
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
*)

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

(* TODO: move *)
val OPTREL_refl = store_thm(
"OPTREL_refl",
``(!x. R x x) ==> !x. OPTREL R x x``,
strip_tac >> Cases >> rw[optionTheory.OPTREL_def])
val _ = export_rewrites["OPTREL_refl"]

val do_app_def = MiniMLTheory.do_app_def
val bind_def = MiniMLTheory.bind_def
val build_rec_env_def = MiniMLTheory.build_rec_env_def

val build_rec_env_closed = store_thm(
"build_rec_env_closed",
``∀defs l.
  EVERY closed (MAP SND l) ∧
  (∀i d x b. i < LENGTH defs ∧ (EL i defs = (d,x,b)) ⇒
   FV b ⊆ set (MAP FST l) ∪ set (MAP FST defs) ∪ {x})
  ⇒ EVERY closed (MAP SND (build_rec_env defs l))``,
rw[build_rec_env_def,bind_def,FOLDR_CONS_triple] >>
rw[MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD] >>
asm_simp_tac(srw_ss())[EVERY_MEM,MEM_MAP,pairTheory.EXISTS_PROD] >>
rw[MEM_EL] >>
rw[Once closed_cases] >- (
  rw[MEM_MAP,pairTheory.EXISTS_PROD,MEM_EL] >>
  PROVE_TAC[]) >>
first_x_assum match_mp_tac >>
PROVE_TAC[])

val do_app_closed = store_thm(
"do_app_closed",
``∀env op v1 v2 env' exp.
  EVERY closed (MAP SND env) ∧
  closed v1 ∧ closed v2 ∧
  (do_app env op v1 v2 = SOME (env',exp))
  ⇒ EVERY closed (MAP SND env')``,
gen_tac >> Cases
>- (
  Cases >> TRY (Cases_on `l`) >>
  Cases >> TRY (Cases_on `l`) >>
  rw[do_app_def] >>
  fs[closed_cases])
>- (
  Cases >> TRY (Cases_on `l`) >>
  Cases >> TRY (Cases_on `l`) >>
  rw[do_app_def] >>
  fs[closed_cases])
>- (
  Cases >> TRY (Cases_on `l`) >>
  Cases >> TRY (Cases_on `l`) >>
  rw[do_app_def] >> fs[]) >>
Cases >> Cases >> rw[do_app_def,bind_def] >> fs[closed_cases] >>
fs[] >> rw[] >>
qmatch_assum_rename_tac `MEM s (MAP FST defs)`[] >>
Cases_on `find_recfun s defs` >> fs[] >>
qmatch_assum_rename_tac `find_recfun s defs = SOME p`[] >>
Cases_on `p` >> fs[] >> rw[] >> rw[Once closed_cases] >>
PROVE_TAC[build_rec_env_closed])

val do_prim_app_FV = store_thm(
"do_prim_app_FV",
``∀env op v1 v2 env' exp.
  (op ≠ Opapp) ∧
  (do_app env op v1 v2 = SOME (env',exp)) ⇒
  (FV exp = {})``,
gen_tac >> Cases >>
Cases >> TRY (Cases_on `l`) >>
Cases >> TRY (Cases_on `l`) >>
rw[do_app_def] >> rw[])

val exp_to_Cexp_thm1 = store_thm(
"exp_to_Cexp_thm1",
``∀cenv env exp res. evaluate cenv env exp res ⇒
  (EVERY closed (MAP SND env)) ∧ (FV exp ⊆ set (MAP FST env)) ∧
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
  `∀n. n < LENGTH es ⇒ FV (EL n es) ⊆ set (MAP FST env)` by (
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
    PROVE_TAC[] ) >>
  fs[] >>
  fs[Once (GSYM RIGHT_EXISTS_IMP_THM),SKOLEM_THM] >>
  qexists_tac `GENLIST f (LENGTH vs)` >>
  fsrw_tac[DNF_ss][MEM_ZIP,EL_MAP,EL_GENLIST,MAP_GENLIST,EL_MAP]) >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[exp_to_Cexp_def,v_to_Cv_def,
     exps_to_Cexps_MAP,
     evaluate_list_with_error,Cevaluate_con,
     Cevaluate_list_with_Cevaluate,Cevaluate_list_with_error] >>
  fs[] >>
  `∀n. n < LENGTH es ⇒ FV (EL n es) ⊆ set (MAP FST env)` by (
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
    PROVE_TAC[] ) >>
  rpt (qpat_assum `X < LENGTH es` mp_tac) >> rw[] >>
  fsrw_tac[ARITH_ss][] >>
  first_x_assum (qspec_then `m` strip_assume_tac) >>
  qmatch_assum_rename_tac `Cevaluate Cenv (exp_to_Cexp m (EL k es)) (Rerr err)`["Cenv"] >>
  qexists_tac `k` >> fs[EL_MAP] >>
  qx_gen_tac `z` >> strip_tac >>
  qpat_assum `∀m. m < k ⇒ P` (qspec_then `z` mp_tac) >> rw[] >>
  first_x_assum (qspec_then `m` strip_assume_tac) >>
  fsrw_tac[ARITH_ss][EL_MAP] >>
  PROVE_TAC[] ) >>
strip_tac >- (
  fs[exp_to_Cexp_def,MEM_MAP,pairTheory.EXISTS_PROD,env_to_Cenv_MAP] >>
  rpt gen_tac >> rpt (disch_then strip_assume_tac) >> qx_gen_tac `m` >>
  rw[alist_to_fmap_MAP_values] >>
  `n ∈ FDOM (alist_to_fmap env)` by (
    rw[MEM_MAP,pairTheory.EXISTS_PROD] >> PROVE_TAC[] ) >>
  rw[o_f_FAPPLY] >>
  PROVE_TAC[ALOOKUP_SOME_FAPPLY_alist_to_fmap,syneq_refl] ) >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[exp_to_Cexp_def,v_to_Cv_def,env_to_Cenv_MAP,LET_THM] >>
  srw_tac[DNF_ss][Once syneq_cases] >>
  rw[FINITE_has_fresh_string,fresh_var_not_in]) >>
strip_tac >- (
  ntac 2 gen_tac >>
  Cases >> fs[exp_to_Cexp_def] >>
  qx_gen_tac `e1` >>
  qx_gen_tac `e2` >>
  rw[LET_THM] >- (
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj1_tac >>
    rw[Cevaluate_list_with_Cevaluate] >>
    rw[Cevaluate_list_with_cons] >>
    rpt (first_x_assum (qspec_then `m` mp_tac)) >>
    rw[] >>
    qmatch_assum_rename_tac `syneq (v_to_Cv m v1) w1`[] >>
    qmatch_assum_rename_tac `syneq (v_to_Cv m v2) w2`[] >>
    qexists_tac `w1` >>
    qexists_tac `w2` >>
    fs[] >>
    qmatch_assum_rename_tac `do_app env (Opn opn) v1 v2 = SOME (env',exp'')` [] >>
    Cases_on `opn` >>
    Cases_on `v1` >> Cases_on `l` >> fs[MiniMLTheory.do_app_def] >>
    Cases_on `v2` >> Cases_on `l` >> fs[] >> rw[] >>
    fs[CevalPrim2_def,doPrim2_def,exp_to_Cexp_def,MiniMLTheory.opn_lookup_def,i0_def,v_to_Cv_def] >>
    rw[] >> fs[v_to_Cv_def,Q.SPEC`CLitv (IntLit x)`syneq_cases,i0_def] >>
    rw[] >> fs[] >> rw[] >> fs[] >> rw[v_to_Cv_def])
  >- (
    qmatch_assum_rename_tac `do_app env (Opb opb) v1 v2 = SOME (env',exp'')` [] >>
    fs[] >>

    do_app_closed
    do_app_FV

    rpt (first_x_assum (qspec_then `m` mp_tac)) >> rw[] >>
    qmatch_assum_rename_tac `syneq (v_to_Cv m v1) w1`[] >>
    qmatch_assum_rename_tac `syneq (v_to_Cv m v2) w2`[] >>
    Cases_on `opb` >> fsrw_tac[DNF_ss][]
    >- tacLt
    >- tacGt
    >- tacLt
    >- tacGt )
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
    sorry)))

val free_vars_remove_mat_vp = store_thm(
"free_vars_remove_mat_vp",
``(∀p fk sk v. free_vars (remove_mat_vp fk sk v p) ⊆
  {v;fk} ∪ (free_vars sk DIFF Cpat_vars p)) ∧
(∀ps fk sk v n. free_vars (remove_mat_con fk sk v n ps) ⊆
  {v;fk} ∪ (free_vars sk DIFF BIGUNION (IMAGE Cpat_vars (set ps))))``,
ho_match_mp_tac (TypeBase.induction_of(``:Cpat``)) >>
strip_tac >- (
  rw[SUBSET_DEF] >> rw[] ) >>
strip_tac >- rw[] >>
strip_tac >- rw[FOLDL_UNION_BIGUNION] >>
strip_tac >- rw[] >>
srw_tac[DNF_ss][LET_THM,SUBSET_DEF] >>
res_tac >> fs[] >>
res_tac >> fs[])

val free_vars_remove_mat = store_thm(
"free_vars_remove_mat",
``(∀exp. free_vars (remove_mat exp) ⊆ free_vars exp) ∧
  (∀v pes. free_vars (remove_mat_var v pes) ⊆ free_vars (CMat v pes))
``,
ho_match_mp_tac remove_mat_ind >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- (
  srw_tac[ETA_ss][FOLDL_UNION_BIGUNION] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP] >>
  PROVE_TAC[] ) >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- (
  srw_tac[ETA_ss][FOLDL_UNION_BIGUNION] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP] >>
  PROVE_TAC[] ) >>
strip_tac >- (
  Cases >>
  srw_tac[ETA_ss][FOLDL_UNION_BIGUNION_paired] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,pairTheory.EXISTS_PROD] >>
  PROVE_TAC[] ) >>
strip_tac >- rw[SUBSET_DEF] >>
strip_tac >- (
  srw_tac[ETA_ss][FOLDL_UNION_BIGUNION] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP] >>
  PROVE_TAC[] ) >>
strip_tac >- (
  rw[SUBSET_DEF] >>
  PROVE_TAC[] ) >>
strip_tac >- (
  srw_tac[ETA_ss][FOLDL_UNION_BIGUNION] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP] >>
  PROVE_TAC[] ) >>
strip_tac >- rw[] >>
srw_tac[ETA_ss][FOLDL_UNION_BIGUNION_paired] >>
fsrw_tac[DNF_ss][SUBSET_DEF,pairTheory.EXISTS_PROD] >>
rw[] >- (
  (free_vars_remove_mat_vp
   |> CONJUNCT1
   |> qspecl_then [`p`,`fk`,`sk`,`v`] mp_tac) >>
  fs[SUBSET_DEF] >>
  disch_then (qspec_then `x` mp_tac) >>
  fs[] >>
  PROVE_TAC[] ) >>
PROVE_TAC[])

(* TODO: move? *)
val Cpmatch_lit_match = store_thm(
"Cpmatch_lit_match",
``(Cpmatch env (CPlit l) v = Cmatch env') = ((v = CLitv l) ∧ (env' = env))``,
Cases_on `v` >> rw[Cpmatch_def,MiniMLTheory.lit_same_type_def] >>
BasicProvers.EVERY_CASE_TAC >>
rw[EQ_IMP_THM])
val _ = export_rewrites["Cpmatch_lit_match"]

val Cpmatch_con_match = store_thm(
"Cpmatch_con_match",
``(Cpmatch env (CPcon n ps) v = Cmatch env') = ∃vs. (v = CConv n vs) ∧ (LENGTH vs = LENGTH ps) ∧ (Cpmatch_list env ps vs = Cmatch env')``,
Cases_on `v` >> fs[Cpmatch_def] >> rw[] >> PROVE_TAC[])
val _ = export_rewrites["Cpmatch_con_match"]

val Cpmatch_list_nil_match = store_thm(
"Cpmatch_list_nil_match",
``((Cpmatch_list env [] vs = Cmatch env') = ((vs = []) ∧ (env' = env))) ∧
  ((Cpmatch_list env ps [] = Cmatch env') = ((ps = []) ∧ (env' = env)))``,
Cases_on `vs` >> Cases_on `ps` >> fs[Cpmatch_def,EQ_IMP_THM])
val _ = export_rewrites["Cpmatch_list_nil_match"]

val result_rel_trans = store_thm(
"result_rel_trans",
``(∀x y z. R x y ∧ R y z ⇒ R x z) ⇒ (∀x y z. result_rel R x y ∧ result_rel R y z ⇒ result_rel R x z)``,
rw[] >>
Cases_on `x` >> fs[] >> rw[] >> fs[] >> PROVE_TAC[])

val result_rel_sym = store_thm(
"result_rel_sym",
``(∀x y. R x y ⇒ R y x) ⇒ (∀x y. result_rel R x y ⇒ result_rel R y x)``,
rw[] >> Cases_on `x` >> fs[])

val Cpat_nice_ind =
TypeBase.induction_of(``:Cpat``)
|> Q.SPECL[`P`,`EVERY P`]
|> SIMP_RULE(srw_ss())[]
|> UNDISCH_ALL
|> CONJUNCT1
|> DISCH_ALL
|> Q.GEN`P`

val remove_mat_con_FOLDR = store_thm(
"remove_mat_con_FOLDR",
``∀ps n fk sk v.
  remove_mat_con fk sk v n ps =
    FOLDR (λ(n,p) r.
      let v' = fresh_var ({v} ∪ free_vars sk ∪ Cpat_vars p) in
      CLet [v'] [CProj (CVar v) n]
        (remove_mat_vp fk r v' p))
      sk (ZIP(GENLIST ($+ n) (LENGTH ps),ps))``,
Induct >- rw[remove_mat_vp_def] >>
rw[remove_mat_vp_def] >>
rw[GENLIST_CONS] >>
`$+ n o SUC = $+ (n + 1)` by (
  rw[FUN_EQ_THM] >>
  srw_tac[ARITH_ss][] ) >>
rw[])

val DRESTRICT_FDOM = store_thm(
"DRESTRICT_FDOM",
``DRESTRICT fm (FDOM fm) = fm``,
SRW_TAC[][GSYM fmap_EQ_THM,DRESTRICT_DEF])

val FRANGE_DRESTRICT_SUBSET = store_thm(
"FRANGE_DRESTRICT_SUBSET",
``FRANGE (DRESTRICT fm s) ⊆ FRANGE fm``,
SRW_TAC[][FRANGE_DEF,SUBSET_DEF,DRESTRICT_DEF] THEN
SRW_TAC[][] THEN PROVE_TAC[])

val Cevaluate_FOLDR_trans = store_thm(
"Cevaluate_FOLDR_trans",
``∀ls.
(∀v. v ∈ FRANGE env ⇒ Cclosed v) ∧
(free_vars (FOLDR f a ls) ⊆ FDOM env) ∧
(∀x exp. free_vars exp ⊆ free_vars (f x exp)) ∧
(∃res'. Cevaluate (DRESTRICT env (free_vars a)) a res ∧ result_rel syneq res res') ∧
(∀x exp res'. Cevaluate (DRESTRICT env (free_vars exp)) exp res' ∧
              (∀v. v ∈ FRANGE env ⇒ Cclosed v) ∧
              (free_vars exp ⊆ FDOM env)
⇒ ∃res''. Cevaluate (DRESTRICT env (free_vars (f x exp))) (f x exp) res'' ∧ result_rel syneq res' res'') ⇒
∃res'. Cevaluate env (FOLDR f a ls) res' ∧ result_rel syneq res res'``,
rw[] >>
Induct_on `ls` >- (
  rw[] >>
  `∃res1. Cevaluate (DRESTRICT env (FDOM env)) a res1 ∧
          result_rel syneq res res1`
  by metis_tac[Cevaluate_super_env,DRESTRICT_FDOM] >>
  metis_tac[DRESTRICT_FDOM]) >>
rw[] >>
`free_vars (FOLDR f a ls) ⊆ FDOM env` by metis_tac[SUBSET_TRANS] >>
fs[] >>
`∃res1.
  Cevaluate (DRESTRICT env (free_vars (FOLDR f a ls))) (FOLDR f a ls)
  res1 ∧ result_rel syneq res'' res1`
by metis_tac[Cevaluate_free_vars_env] >>
first_x_assum (qspecl_then [`h`,`FOLDR f a ls`,`res1`] mp_tac) >>
rw[] >>
`result_rel syneq res res1` by PROVE_TAC[syneq_trans,result_rel_trans] >>
`result_rel syneq res res'''` by PROVE_TAC[syneq_trans,result_rel_trans] >>
qho_match_abbrev_tac `∃res'. Cevaluate env exp res' ∧ result_rel syneq res res'` >>
qsuff_tac `∃res'. Cevaluate (DRESTRICT env (FDOM env)) exp res' ∧ result_rel syneq res''' res'` >- (
  rw[DRESTRICT_FDOM] >>
  PROVE_TAC[syneq_trans,result_rel_trans] ) >>
match_mp_tac Cevaluate_super_env >>
rw[DRESTRICT_FDOM])

(*
val remove_mat_vp_match = store_thm(
"remove_mat_vp_match",
``(∀p env n fk sk env' res.
  n ∈ FDOM env ∧ (Cpmatch FEMPTY p (env ' n) = Cmatch env') ∧
  n ∉ Cpat_vars p ∧
  Cevaluate (env' ⊌ env) sk res
⇒ ∃res'. Cevaluate env (remove_mat_vp fk sk n p) res' ∧
         result_rel syneq res res')``,
ho_match_mp_tac Cpat_nice_ind >>
strip_tac >- (
  rw[remove_mat_vp_def,Cpmatch_def,LET_THM] >>
  rw[Cevaluate_let_cons] >>
  fs[FUNION_FUPDATE_1,FUNION_FEMPTY_1] >>
  PROVE_TAC[result_rel_refl,syneq_refl]) >>
strip_tac >- (
  rw[remove_mat_vp_def,Cpmatch_def,LET_THM] >>
  srw_tac[DNF_ss][Once Cevaluate_cases] >>
  disj1_tac >>
  CONV_TAC SWAP_EXISTS_CONV >>
  qexists_tac `T` >>
  fs[FUNION_FEMPTY_1] >>
  rw[Once Cevaluate_cases] >>
  rw[Cevaluate_list_with_Cevaluate] >>
  rw[Cevaluate_list_with_cons] >>
  PROVE_TAC[result_rel_refl,syneq_refl] ) >>
gen_tac >> strip_tac >>
rw[remove_mat_vp_def,Cpmatch_def,LET_THM] >>
fs[FOLDL_UNION_BIGUNION] >>
srw_tac[DNF_ss][Once Cevaluate_cases] >>
srw_tac[DNF_ss][Once Cevaluate_cases] >>
disj1_tac >>
qmatch_assum_rename_tac `env ' v = CConv m vs`[] >>
qspecl_then[`l`,`fk`,`sk`,`v`,`0`] assume_tac
  (CONJUNCT2 free_vars_remove_mat_vp) >>
fs[remove_mat_con_FOLDR] >>
ho_match_mp_tac Cevaluate_FOLDR_trans
*)

val DROP_NIL = store_thm(
"DROP_NIL",
``∀ls n. (DROP n ls = []) = (n ≥ LENGTH ls)``,
Induct >> rw[] >>
srw_tac[ARITH_ss][])

(*
val remove_mat_vp_match = store_thm(
"remove_mat_vp_match",
``(∀p env n fk sk env' res.
  n ∈ FDOM env ∧ (Cpmatch FEMPTY p (env ' n) = Cmatch env') ∧
  n ∉ Cpat_vars p ∧
  Cevaluate (env' ⊌ env) sk res
⇒ ∃res'. Cevaluate env (remove_mat_vp fk sk n p) res' ∧
         result_rel syneq res res') ∧
(∀ps i env n fk sk m vs env' res.
 n ∈ FDOM env ∧ (env ' n = CConv m vs) ∧ i ≤ LENGTH vs ∧
 (LENGTH ps = LENGTH vs) ∧
 n ∉ BIGUNION (IMAGE Cpat_vars (set ps)) ∧
 (Cpmatch_list FEMPTY (DROP i ps) (DROP i vs) = Cmatch env') ∧
 Cevaluate (env' ⊌ env) sk res
 ⇒ ∃res'. Cevaluate env (remove_mat_con fk sk n i (DROP i ps)) res' ∧
          result_rel syneq res res')``,
ho_match_mp_tac (TypeBase.induction_of(``:Cpat``)) >>
strip_tac >- (
  rw[remove_mat_vp_def,Cpmatch_def,LET_THM] >>
  rw[Cevaluate_let_cons] >>
  fs[FUNION_FUPDATE_1,FUNION_FEMPTY_1] >>
  PROVE_TAC[result_rel_refl,syneq_refl]) >>
strip_tac >- (
  rw[remove_mat_vp_def,Cpmatch_def,LET_THM] >>
  srw_tac[DNF_ss][Once Cevaluate_cases] >>
  disj1_tac >>
  CONV_TAC SWAP_EXISTS_CONV >>
  qexists_tac `T` >>
  fs[FUNION_FEMPTY_1] >>
  rw[Once Cevaluate_cases] >>
  rw[Cevaluate_list_with_Cevaluate] >>
  rw[Cevaluate_list_with_cons] >>
  PROVE_TAC[result_rel_refl,syneq_refl] ) >>
strip_tac >- (
  rw[remove_mat_vp_def,Cpmatch_def,LET_THM] >>
  srw_tac[DNF_ss][Once Cevaluate_cases] >>
  disj1_tac >>
  fs[FOLDL_UNION_BIGUNION] >>
  srw_tac[DNF_ss][Once Cevaluate_cases] >>
  first_x_assum (qspec_then `0` mp_tac) >>
  rw[]) >>
strip_tac >-
  ( fs[FUNION_FEMPTY_1] >> PROVE_TAC[result_rel_refl,syneq_refl]) >>
rpt gen_tac >> strip_tac >>
rpt gen_tac >>
Cases_on `i = LENGTH vs` >-(
  fs[rich_listTheory.BUTFIRSTN_LENGTH_NIL] >>
  rw[] >> fs[FUNION_FEMPTY_1] >>
  PROVE_TAC[result_rel_refl,syneq_refl] ) >>
strip_tac >>
qabbrev_tac `pps = (p::ps)` >>
`i < LENGTH vs` by (
  fs[arithmeticTheory.LESS_OR_EQ] >>
  fs[] ) >>
`DROP i pps = EL i pps::DROP (SUC i) pps` by (
  match_mp_tac rich_listTheory.BUTFIRSTN_CONS_EL >>
  rw[] ) >>
rw[LET_THM] >>
srw_tac[DNF_ss][Once Cevaluate_cases,LET_THM] >>
disj1_tac >>
srw_tac[DNF_ss][Once Cevaluate_cases] >>
`DROP i vs = EL i vs::DROP (SUC i) vs` by (
  match_mp_tac rich_listTheory.BUTFIRSTN_CONS_EL >>
  rw[] ) >>
fs[Cpmatch_def] >>
Cases_on `Cpmatch FEMPTY (EL i pps) (EL i vs)` >> fs[] >>
qpat_assum `Cpmatch_list X Y Z = A` mp_tac >>
rw[Once Cpmatch_FEMPTY] >>
Cases_on `Cpmatch_list FEMPTY (DROP (SUC i) pps) (DROP (SUC i) vs)` >> fs[] >>
qmatch_abbrev_tac `∃res'. Cevaluate env0 (remove_mat_vp fk sk0 n0 ip) res' ∧ result_rel syneq res res'` >>
`n0 ∉ {n} ∪ free_vars sk ∪ Cpat_vars ip` by (
  qunabbrev_tac`n0` >>
  match_mp_tac fresh_var_not_in >>
  match_mp_tac FINITE_has_fresh_string >>
  rw[] ) >>
qmatch_assum_rename_tac `Cpmatch_list FEMPTY (DROP (SUC i) pps) (DROP (SUC i) vs) = Cmatch env1`[]
qmatch_assum_rename_tac `Cpmatch FEMPTY ip (EL i vs) = Cmatch env2`[] >>
first_x_assum (qspecl_then
  [`env0`,`n0`,`fk`,`sk0`] mp_tac) >>
fsrw_tac[][Abbr`env0`,Abbr`sk0`] >>
Q.PAT_ABBREV_TAC `env0 = env |+ kv` >>
first_x_assum (qspecl_then
  [`i+1`,`env2 ⊌ env0`,`n`,`fk`,`sk`,`m`,`vs`,`env1`] mp_tac) >>
`n ∉ Cpat_vars p` by PROVE_TAC[] >>
imp_res_tac Cpmatch_pat_vars >> fs[] >>
fs[Abbr`env0`,FAPPLY_FUPDATE_THM,FUNION_DEF] >>
fsrw_tac[ARITH_ss][] >>
`∀s. n ∉ s ∨ ∀x. s ≠ Cpat_vars x ∨ ¬MEM x ps` by PROVE_TAC[] >> fs[] >>
fs[arithmeticTheory.ADD1] >>
qpat_assum `env1 ⊌ env2 = X` (assume_tac o SYM) >>
fs[FUNION_ASSOC] >>
qsuff_tac `∃res'. Cevaluate (env1 ⊌ env2 ⊌ env |+ (n0,EL i vs)) sk res' ∧ result_rel syneq res res'` >- (
  rw[] >>
  res_tac >>
  res_tac >>
  METIS_TAC[syneq_trans,result_rel_trans,syneq_sym,result_rel_sym] ) >>
fsrw_tac[DNF_ss][FUNION_FUPDATE_2] >>
rw[] >- PROVE_TAC[]

match_mp_tac Cevaluate_FUPDATE
*)

(*
val remove_mat_thm1 = store_thm(
"remove_mat_thm1",
``∀env exp res. Cevaluate env exp res ⇒
  (* free_vars exp ⊆ FDOM env ⇒ *)
  ∃res'. Cevaluate env (remove_mat exp) res' ∧ result_rel syneq res res'``,
ho_match_mp_tac Cevaluate_nice_ind >>
strip_tac >- rw[remove_mat_def] >>
strip_tac >- rw[remove_mat_def] >>
strip_tac >- rw[remove_mat_def] >>
strip_tac >- (
  rw[remove_mat_def,Cevaluate_con,EL_MAP,
     Cevaluate_list_with_Cevaluate,Cevaluate_list_with_value] >>
  fsrw_tac[DNF_ss][] >>
  rw[syneq_cases,EVERY2_EVERY] >>
  fs[GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM] >>
  qexists_tac `GENLIST f (LENGTH vs)` >>
  fsrw_tac[DNF_ss][EVERY_MEM,MEM_ZIP]) >>
strip_tac >- (
  rw[remove_mat_def,Cevaluate_con,EL_MAP,
     Cevaluate_list_with_Cevaluate,Cevaluate_list_with_error] >>
  fsrw_tac[SATISFY_ss,ETA_ss][] >>
  metis_tac[EL_MAP,arithmeticTheory.LESS_TRANS]) >>
strip_tac >- (
  srw_tac[DNF_ss][remove_mat_def,Cevaluate_tageq] >>
  fs[syneq_cases] >>
  PROVE_TAC[] ) >>
strip_tac >- (
  rw[remove_mat_def,Cevaluate_tageq] ) >>
strip_tac >- (
  srw_tac[DNF_ss][remove_mat_def,Cevaluate_proj] >>
  qspec_then `CConv m vs` (fn th => fs[SIMP_RULE(srw_ss())[]th]) syneq_cases >>
  fs[EVERY2_EVERY,EVERY_MEM] >>
  qpat_assum `LENGTH vs = LENGTH vs2` assume_tac >>
  fsrw_tac[DNF_ss][MEM_ZIP] >>
  PROVE_TAC[] ) >>
strip_tac >- (
  rw[remove_mat_def,Cevaluate_proj] ) >>
strip_tac >- (
  rw[remove_mat_def] ) >>
strip_tac >- (
  rw[remove_mat_def,LET_THM] >>
  rw[Once Cevaluate_cases] >>
  fs[Once Cpmatch_FEMPTY] >>
  Cases_on `Cpmatch FEMPTY p (env ' n)` >> fs[] >> rw[] >>

*)

val bc_finish_def = Define`
  bc_finish s1 s2 = bc_next^* s1 s2 ∧ ∀s3. ¬bc_next s2 s3`

(*
val compile_thm1 = store_thm(
"compile_thm1",
``∀env exp res. Cevaluate env exp res ⇒
  ∀v. (res = Rval v) ∧ (∀s. exp ≠ CDecl s) ⇒
    ∀cs cs'. (cs' = compile cs exp) ⇒
      ∃c. (cs'.code = (REVERSE c)++cs.code) ∧
      ∀b1. ∃b2. bc_finish (b1 with <| code := b1.code ++ c |>) b2 ∧
                ∃bv. (b2.stack = bv::b1.stack) ∧
                     bceqv cs'.inst_length b2.code v bv``,
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
