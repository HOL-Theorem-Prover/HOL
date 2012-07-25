open HolKernel bossLib boolLib listTheory pred_setTheory finite_mapTheory alistTheory intLib lcsymtacs
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

val fresh_var_not_in_any = store_thm(
"fresh_var_not_in_any",
``FINITE s ∧ t ⊆ s ⇒ fresh_var s ∉ t``,
PROVE_TAC[fresh_var_not_in,SUBSET_DEF,FINITE_has_fresh_string])

val free_vars_remove_mat_vp = store_thm(
"free_vars_remove_mat_vp",
``(∀p fk sk v.
    (free_vars (remove_mat_vp fk sk v p) DIFF {v;fk} =
     free_vars sk DIFF Cpat_vars p DIFF {v;fk})) ∧
  (∀ps fk sk v n.
   (free_vars (remove_mat_con fk sk v n ps) DIFF {v;fk} =
    free_vars sk DIFF BIGUNION (IMAGE Cpat_vars (set ps)) DIFF {v;fk}))``,
ho_match_mp_tac (TypeBase.induction_of(``:Cpat``)) >>
strip_tac >- (
  rw[EXTENSION] >> PROVE_TAC[] ) >>
strip_tac >- (
  rw[EXTENSION] >> PROVE_TAC[] ) >>
strip_tac >- (
  rw[FOLDL_UNION_BIGUNION] >>
  fs[EXTENSION] >> METIS_TAC[] ) >>
strip_tac >- (
  rw[EXTENSION] >> PROVE_TAC[] ) >>
rw[LET_THM] >>
qmatch_abbrev_tac `free_vars (remove_mat_vp fk sk0 v0 p) DIFF {v0} UNION {v} DIFF {v; fk} = vs DIFF {v; fk}` >>
simp_tac std_ss [Once EXTENSION] >>
qx_gen_tac `x` >>
fs[] >>
Cases_on `x=v` >> fs[] >>
Cases_on `x=fk` >> fs[] >>
Cases_on `x=v0` >> fs[] >- (
  unabbrev_all_tac >>
  match_mp_tac fresh_var_not_in_any >>
  fs[SUBSET_DEF] ) >>
qpat_assum `∀fk sk v. P = Q` (qspecl_then [`fk`,`sk0`,`v0`] mp_tac) >>
simp_tac std_ss [Once EXTENSION] >>
disch_then (qspec_then `x` mp_tac) >>
fs[] >> strip_tac >>
first_x_assum (qspecl_then [`fk`,`sk`,`v`,`n+1`] mp_tac) >>
simp_tac std_ss [Once EXTENSION] >>
disch_then (qspec_then `x` mp_tac) >>
fs[] >> strip_tac >>
fs[Abbr`vs`] >> PROVE_TAC[])

val free_vars_remove_mat_vp_SUBSET = store_thm(
"free_vars_remove_mat_vp_SUBSET",
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

val fsd = full_simp_tac std_ss

val free_vars_remove_mat_var = store_thm(
"free_vars_remove_mat_var",
``∀v pes. free_vars (remove_mat_var v pes) DIFF {v} =
  BIGUNION (IMAGE (λ(p,e). free_vars e DIFF Cpat_vars p) (set pes)) DIFF {v}``,
ho_match_mp_tac remove_mat_var_ind >>
strip_tac >- rw[remove_mat_var_def] >>
rw[remove_mat_var_def] >>
rw[] >>
full_simp_tac std_ss [EXTENSION,IN_UNION,IN_DIFF,IN_SING] >>
qx_gen_tac `x` >>
Cases_on `x=v` >> fsd[] >>
Cases_on `x=fk` >> fsd[] >- (
  `fk ∉ free_vars sk` by (
    unabbrev_all_tac >>
    match_mp_tac fresh_var_not_in_any >>
    fs[SUBSET_DEF] ) >>
  fsd[] >>
  PROVE_TAC[] ) >>
mp_tac (CONJUNCT1 free_vars_remove_mat_vp) >>
fsd[EXTENSION,IN_DIFF,IN_INSERT,IN_SING] >>
metis_tac[])

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
  qmatch_abbrev_tac `free_vars (remove_mat_var v pe) DIFF x ∪ y = z` >>
  qspecl_then [`v`,`pe`] mp_tac free_vars_remove_mat_var >>
  asm_simp_tac std_ss [EXTENSION,IN_DIFF,IN_SING,IN_UNION] >>
  strip_tac >>
  qx_gen_tac `u` >>
  Cases_on `u ∈ y` >> fsd[] >>
  qunabbrev_tac `y` >>
  fsd[pairTheory.FORALL_PROD] >>
  Cases_on `u=v` >> fsd[] >- (
    qunabbrev_tac`v` >>
    match_mp_tac fresh_var_not_in_any >>
    qunabbrev_tac`x` >>
    qunabbrev_tac`z` >>
    pop_assum kall_tac >>
    ntac 2 (pop_assum kall_tac) >>
    fsrw_tac[DNF_ss][SUBSET_DEF,pairTheory.FORALL_PROD,
                     Abbr`pe`,Cpes_vars_thm] >>
    fsrw_tac[DNF_ss][MAP_MAP_o,combinTheory.o_DEF,
                     pairTheory.LAMBDA_PROD] >>
    fsrw_tac[DNF_ss][MEM_MAP,pairTheory.EXISTS_PROD] >>
    fsrw_tac[DNF_ss][pairTheory.UNCURRY] >>
    map_every qx_gen_tac [`x`,`y`,`z`] >>
    strip_tac >>
    disj2_tac >>
    map_every qexists_tac [`y`,`z`] >>
    rw[] >> PROVE_TAC[] ) >>
  fsrw_tac[DNF_ss][pairTheory.EXISTS_PROD] >>
  fsrw_tac[DNF_ss][Abbr`pe`,MEM_MAP,pairTheory.EXISTS_PROD] >>
  qunabbrev_tac`x` >>
  qunabbrev_tac`z` >>
  fsrw_tac[DNF_ss][pairTheory.UNCURRY] >>
  rw[Once CONJ_ASSOC] >>
  qho_match_abbrev_tac `
    (∃p1 p2. A p1 p2 ∧ MEM (p1,p2) pes) =
    (∃p1 p2. B p1 p2 ∧ MEM (p1,p2) pes)` >>
  (qsuff_tac `∀p1 p2. MEM (p1,p2) pes ⇒ (A p1 p2 = B p1 p2)` >- PROVE_TAC[]) >>
  srw_tac[DNF_ss][Abbr`A`,Abbr`B`] >>
  first_x_assum (qspecl_then [`p1`,`p2`] mp_tac) >>
  rw[] >>
  qabbrev_tac `q = pat_to_Cpat s [] p1` >>
  PairCases_on `q` >> fs[] >>
  PROVE_TAC[Cpat_vars_pat_to_Cpat])
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
val find_recfun_def = MiniMLTerminationTheory.find_recfun_def
val do_log_def = MiniMLTheory.do_log_def
val do_if_def = MiniMLTheory.do_if_def

val build_rec_env_closed = store_thm(
"build_rec_env_closed",
``∀defs l.
  EVERY closed (MAP SND l) ∧
  ALL_DISTINCT (MAP FST defs) ∧
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

val build_rec_env_dom = store_thm(
"build_rec_env_dom",
``MAP FST (build_rec_env defs env) = MAP FST defs ++ MAP FST env``,
rw[build_rec_env_def,bind_def,FOLDR_CONS_triple] >>
rw[MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD] >>
rw[FST_triple])
val _ = export_rewrites["build_rec_env_dom"]

val find_recfun_ALOOKUP = store_thm(
"find_recfun_ALOOKUP",
``find_recfun = combin$C ALOOKUP``,
rw[FUN_EQ_THM] >>
qmatch_rename_tac `find_recfun n funs = ALOOKUP funs n`[] >>
qid_spec_tac `n` >>
Induct_on `funs` >- rw[find_recfun_def] >>
qx_gen_tac `d` >>
PairCases_on `d` >>
rw[find_recfun_def])
val _ = export_rewrites["find_recfun_ALOOKUP"]

val do_app_closed = store_thm(
"do_app_closed",
``∀env op v1 v2 env' exp.
  EVERY closed (MAP SND env) ∧
  closed v1 ∧ closed v2 ∧
  (do_app env op v1 v2 = SOME (env',exp))
  ⇒ EVERY closed (MAP SND env') ∧
    FV exp ⊆ set (MAP FST env')``,
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
rw[Once INSERT_SING_UNION,Once UNION_COMM] >>
qmatch_assum_rename_tac `MEM s (MAP FST defs)`[] >>
Cases_on `ALOOKUP defs s` >> fs[] >>
qmatch_assum_rename_tac `ALOOKUP defs d = SOME p`[] >>
Cases_on `p` >> fs[] >> rw[] >> rw[Once closed_cases] >>
TRY (qmatch_abbrev_tac `EVERY closed X` >>
     PROVE_TAC[build_rec_env_closed]) >>
imp_res_tac ALOOKUP_MEM >>
fsrw_tac[DNF_ss][MEM_EL] >>
fsrw_tac[DNF_ss][SUBSET_DEF] >>
PROVE_TAC[])

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

val do_log_FV = store_thm(
"do_log_FV",
``(do_log op v e2 = SOME exp) ⇒
  (FV exp ⊆ FV e2)``,
fs[do_log_def] >>
BasicProvers.EVERY_CASE_TAC >>
rw[] >>rw[])

val do_if_FV = store_thm(
"do_if_FV",
``(do_if v e2 e3 = SOME e) ⇒
  (FV e ⊆ FV e2 ∪ FV e3)``,
fs[do_if_def] >>
BasicProvers.EVERY_CASE_TAC >>
rw[] >>rw[])

val closed_lit = save_thm(
"closed_lit",
SIMP_RULE(srw_ss())[]
(Q.SPEC`Litv l`closed_cases))
val _ = export_rewrites["closed_lit"]

val closed_conv = save_thm(
"closed_conv",
SIMP_RULE(srw_ss())[]
(Q.SPEC`Conv cn vs`closed_cases))
val _ = export_rewrites["closed_conv"]

(* TODO: move *)
val pmatch_def = MiniMLTerminationTheory.pmatch_def
val pmatch_ind = MiniMLTerminationTheory.pmatch_ind
val lit_same_type_def = MiniMLTheory.lit_same_type_def

val pmatch_plit = store_thm(
"pmatch_plit",
``(pmatch cenv (Plit l) v env = r) =
  (((v = Litv l) ∧ (r = Match env)) ∨
   ((∃l'. (v = Litv l') ∧ lit_same_type l l' ∧ l ≠ l') ∧
    (r = No_match)) ∨
   ((∀l'. (v = Litv l') ⇒ ¬lit_same_type l l') ∧ (r = Match_type_error)))``,
Cases_on `v` >> rw[pmatch_def,EQ_IMP_THM] >>
Cases_on `l` >> fs[lit_same_type_def])

(*
val pmatch_pcon = store_thm(
"pmatch_pcon",
``(pmatch cenv (Pcon n ps) v env = r) =
*)

val map_match_def = Define`
  (map_match f (Match env) = Match (f env)) ∧
  (map_match f x = x)`
val _ = export_rewrites["map_match_def"]


(* TODO: move *)
val DROP_APPEND1 = rich_listTheory.BUTFIRSTN_APPEND1
val DROP_APPEND2 = rich_listTheory.BUTFIRSTN_APPEND2
val DROP_LENGTH_NIL = rich_listTheory.BUTFIRSTN_LENGTH_NIL

val pmatch_APPEND = store_thm(
"pmatch_APPEND",
``(∀cenv p v env n.
    (pmatch cenv p v env =
     map_match (combin$C APPEND (DROP n env)) (pmatch cenv p v (TAKE n env)))) ∧
  (∀cenv ps vs env n.
    (pmatch_list cenv ps vs env =
     map_match (combin$C APPEND (DROP n env)) (pmatch_list cenv ps vs (TAKE n env))))``,
ho_match_mp_tac pmatch_ind >>
strip_tac >- rw[pmatch_def,bind_def] >>
strip_tac >- rw[pmatch_def] >>
strip_tac >- (
  rw[pmatch_def] >>
  Cases_on `ALOOKUP cenv n` >> fs[] >>
  PairCases_on `x` >> fs[] >>
  rw[] >> fs[] >>
  Cases_on `ALOOKUP cenv n'` >> fs[] >>
  PairCases_on `x` >> fs[] >>
  rw[] >> fs[] ) >>
strip_tac >- rw[pmatch_def] >>
strip_tac >- rw[pmatch_def] >>
strip_tac >- rw[pmatch_def] >>
strip_tac >- rw[pmatch_def] >>
strip_tac >- rw[pmatch_def] >>
strip_tac >- rw[pmatch_def] >>
strip_tac >- rw[pmatch_def] >>
strip_tac >- (
  rw[pmatch_def] >>
  Cases_on `pmatch cenv p v (TAKE n env)` >> fs[] >>
  Cases_on `pmatch cenv p v env` >> fs[] >>
  TRY (first_x_assum (qspec_then `n` mp_tac) >> rw[] >> NO_TAC) >>
  first_x_assum (qspec_then `n` mp_tac) >> rw[] >>
  first_x_assum (qspec_then `LENGTH l` mp_tac) >> rw[] >>
  rw[TAKE_APPEND1,DROP_APPEND1,DROP_LENGTH_NIL] ) >>
strip_tac >- rw[pmatch_def] >>
strip_tac >- rw[pmatch_def])

val pmatch_nil = save_thm("pmatch_nil",
  LIST_CONJ [
    pmatch_APPEND
    |> CONJUNCT1
    |> Q.SPECL[`cenv`,`p`,`v`,`env`,`0`]
    |> SIMP_RULE(srw_ss())[]
  ,
    pmatch_APPEND
    |> CONJUNCT2
    |> Q.SPECL[`cenv`,`ps`,`vs`,`env`,`0`]
    |> SIMP_RULE(srw_ss())[]
  ])

val pmatch_closed = store_thm("pmatch_closed",
  ``(∀cenv p v env env'.
      EVERY closed (MAP SND env) ∧ closed v ∧
      (pmatch cenv p v env = Match env') ⇒
      EVERY closed (MAP SND env') ∧
      (set (MAP FST env') = pat_vars p ∪ set (MAP FST env))) ∧
    (∀cenv ps vs env env'.
      EVERY closed (MAP SND env) ∧ EVERY closed vs ∧
      (pmatch_list cenv ps vs env = Match env') ⇒
      EVERY closed (MAP SND env') ∧
      (set (MAP FST env') = BIGUNION (IMAGE pat_vars (set ps)) ∪ set (MAP FST env)))``,
  ho_match_mp_tac pmatch_ind >>
  strip_tac >- (
    rw[pmatch_def,bind_def] >>
    rw[] >> rw[EXTENSION] ) >>
  strip_tac >- (
    rw[pmatch_def] >> rw[] ) >>
  strip_tac >- (
    rpt gen_tac >> fs[] >>
    Cases_on `ALOOKUP cenv n` >> fs[] >- (
      rw[pmatch_def] ) >>
    qmatch_assum_rename_tac `ALOOKUP cenv n = SOME p`[] >>
    PairCases_on `p` >> fs[] >>
    Cases_on `ALOOKUP cenv n'` >> fs[] >- (
      rw[pmatch_def] ) >>
    qmatch_assum_rename_tac `ALOOKUP cenv n' = SOME p`[] >>
    PairCases_on `p` >> fs[] >>
    rw[pmatch_def] >>
    srw_tac[ETA_ss][] ) >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- ( rw[pmatch_def] >> rw[] ) >>
  strip_tac >- (
    rpt gen_tac >>
    strip_tac >>
    simp_tac(srw_ss())[pmatch_def] >>
    Cases_on `pmatch cenv p v env` >> fs[] >>
    qmatch_assum_rename_tac `pmatch cenv p v env = Match env0`[] >>
    Cases_on `pmatch_list cenv ps vs env0` >> fs[] >>
    strip_tac >> fs[] >>
    PROVE_TAC[UNION_COMM,UNION_ASSOC]) >>
  rw[pmatch_def])

val evaluate_closed = store_thm(
"evaluate_closed",
``∀cenv env exp res.
  evaluate cenv env exp res ⇒
  FV exp ⊆ set (MAP FST env) ∧
  EVERY closed (MAP SND env) ⇒
  every_result closed res``,
ho_match_mp_tac evaluate_nice_ind >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[] >>
  fs[evaluate_list_with_EVERY] >>
  qpat_assum `LENGTH X = Y` assume_tac >>
  fsrw_tac[DNF_ss][EVERY_MEM,MEM_ZIP,EL_MAP] >>
  rw[MEM_EL] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
  PROVE_TAC[]) >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[] >>
  imp_res_tac ALOOKUP_MEM >>
  fs[EVERY_MEM,MEM_MAP,pairTheory.EXISTS_PROD] >>
  PROVE_TAC[]) >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[] >>
  rw[Once closed_cases] >>
  fsrw_tac[DNF_ss][SUBSET_DEF] >>
  PROVE_TAC[]) >>
strip_tac >- (
  rw[] >> fs[] >>
  PROVE_TAC[do_app_closed]) >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[] >> fs[] >>
  PROVE_TAC[do_log_FV,SUBSET_TRANS]) >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[] >> fs[] >>
  PROVE_TAC[do_if_FV,SUBSET_DEF,IN_UNION]) >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- (
  gen_tac >>
  CONV_TAC (RESORT_FORALL_CONV
    (uncurry cons o pluck (equal "pes" o fst o dest_var))) >>
  Induct >- rw[Once evaluate_match_with_cases] >>
  rpt gen_tac >>
  strip_tac >>
  pop_assum mp_tac >>
  rw[Once evaluate_match_with_cases] >> rw[] >- (
    fs[] >>
    first_x_assum match_mp_tac >>
    imp_res_tac (CONJUNCT1 pmatch_closed) >>
    fs[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    PROVE_TAC[] ) >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  rw[] >>
  map_every qexists_tac[`env`,`exp`,`v`] >>
  fs[] ) >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[bind_def] >>
  fs[] >>
  fsrw_tac[DNF_ss][SUBSET_DEF] >>
  PROVE_TAC[]) >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[] >>
  fs[LIST_TO_SET_MAP] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,pairTheory.EXISTS_PROD] >>
  first_x_assum match_mp_tac >>
  conj_tac >- PROVE_TAC[] >>
  match_mp_tac build_rec_env_closed >>
  fs[LIST_TO_SET_MAP] >>
  fsrw_tac[DNF_ss][MEM_EL,SUBSET_DEF,FST_triple] >>
  metis_tac[pairTheory.FST,pairTheory.PAIR_EQ,pairTheory.pair_CASES]) >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- rw[evaluate_list_with_cons] >>
strip_tac >- rw[evaluate_list_with_cons] >>
strip_tac >- rw[evaluate_list_with_cons] >>
strip_tac >- rw[Once evaluate_match_with_cases] >>
strip_tac >- rw[Once evaluate_match_with_cases] >>
strip_tac >- (
  rw[] >> rw[Once evaluate_match_with_cases] ) >>
strip_tac >- (
  rw[] >> rw[Once evaluate_match_with_cases] ) >>
strip_tac >- (
  rw[] >> rw[Once evaluate_match_with_cases] ))

val do_Opapp_SOME_CRecClos = store_thm(
"do_Opapp_SOME_CRecClos",
``(do_app env Opapp v1 v2 = SOME (env',exp'')) ∧
  syneq (v_to_Cv m v1) w1 ⇒
  ∃env'' ns' defs n.
    (w1 = CRecClos env'' ns' defs n)``,
Cases_on `v1` >> rw[do_app_def,v_to_Cv_def,LET_THM] >>
fs[defs_to_Cdefs_MAP, syneq_cases])

val FRANGE_alist_to_fmap_SUBSET = store_thm(
"FRANGE_alist_to_fmap_SUBSET",
``FRANGE (alist_to_fmap ls) ⊆ IMAGE SND (set ls)``,
srw_tac[DNF_ss][FRANGE_DEF,SUBSET_DEF,pairTheory.EXISTS_PROD] >>
qmatch_assum_rename_tac `MEM z (MAP FST ls)`[] >>
qexists_tac `z` >>
match_mp_tac alist_to_fmap_FAPPLY_MEM >>
rw[])

val FRANGE_FUPDATE_SUBSET = store_thm(
"FRANGE_FUPDATE_SUBSET",
``FRANGE (fm |+ kv) ⊆ FRANGE fm ∪ {SND kv}``,
Cases_on `kv` >>
rw[FRANGE_DEF,SUBSET_DEF,DOMSUB_FAPPLY_THM] >>
rw[] >> PROVE_TAC[])

val IN_FRANGE_alist_to_fmap_suff = store_thm(
"IN_FRANGE_alist_to_fmap_suff",
``(∀v. MEM v (MAP SND ls) ⇒ P v) ⇒ (∀v. v ∈ FRANGE (alist_to_fmap ls) ⇒ P v)``,
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_alist_to_fmap_SUBSET) >>
fs[MEM_MAP] >>
PROVE_TAC[])

val IN_FRANGE_FUPDATE_suff = store_thm(
"IN_FRANGE_FUPDATE_suff",
`` (∀v. v ∈ FRANGE fm ⇒ P v) ∧ (P (SND kv))
⇒ (∀v. v ∈ FRANGE (fm |+ kv) ⇒ P v)``,
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_FUPDATE_SUBSET) >>
fs[])

val DRESTRICT_FDOM = store_thm(
"DRESTRICT_FDOM",
``!f.DRESTRICT f (FDOM f) = f``,
SRW_TAC[][GSYM fmap_EQ_THM,DRESTRICT_DEF])

val Cevaluate_any_super_env = save_thm(
"Cevaluate_any_super_env",
Cevaluate_super_env
|> Q.SPECL[`FDOM (env:string|->Cv)`,`env:string|->Cv`]
|> SIMP_RULE(srw_ss())[DRESTRICT_FDOM,GSYM AND_IMP_INTRO]
|> SPEC_ALL |> UNDISCH_ALL |> DISCH_ALL
|> Q.GEN`res` |> Q.GEN`exp` |> Q.GEN`env`
|> SIMP_RULE(srw_ss())[AND_IMP_INTRO])

val result_rel_trans = store_thm(
"result_rel_trans",
``(∀x y z. R x y ∧ R y z ⇒ R x z) ⇒ (∀x y z. result_rel R x y ∧ result_rel R y z ⇒ result_rel R x z)``,
rw[] >>
Cases_on `x` >> fs[] >> rw[] >> fs[] >> PROVE_TAC[])

val result_rel_sym = store_thm(
"result_rel_sym",
``(∀x y. R x y ⇒ R y x) ⇒ (∀x y. result_rel R x y ⇒ result_rel R y x)``,
rw[] >> Cases_on `x` >> fs[])

val result_rel_syneq_trans = save_thm(
"result_rel_syneq_trans",
result_rel_trans
|> Q.GEN`R`
|> Q.ISPEC`syneq`
|> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
|> UNDISCH
|> PROVE_HYP (SIMP_RULE (std_ss++DNF_ss) []syneq_trans)
|> SIMP_RULE std_ss [AND_IMP_INTRO])

val result_rel_syneq_sym = save_thm(
"result_rel_syneq_sym",
result_rel_sym
|> Q.GEN`R`
|> Q.ISPEC`syneq`
|> SIMP_RULE std_ss[syneq_sym])

val Cevaluate_syneq_env = save_thm(
"Cevaluate_syneq_env",
Cevaluate_any_env
|> SPEC_ALL
|> UNDISCH_ALL
|> SPEC_ALL
|> UNDISCH_ALL
|> Q.SPEC`FEMPTY`
|> SIMP_RULE (srw_ss()) [FUNION_FEMPTY_2]
|> DISCH_ALL
|> SIMP_RULE (srw_ss()) [AND_IMP_INTRO,GSYM CONJ_ASSOC]
|> Q.GEN`res` |> Q.GEN`exp` |> Q.GEN`env` |> Q.GEN`env'`)

val LEAST_BOUND = store_thm(
"LEAST_BOUND",
``∀P n. P n ⇒ ($LEAST P) ≤ n ∧ ($LEAST P = $LEAST (λm. P m ∧ m ≤ n))``,
rpt gen_tac >>
strip_tac >>
conj_tac >- (
  spose_not_then strip_assume_tac >>
  `n < $LEAST P` by DECIDE_TAC >>
  PROVE_TAC[whileTheory.LESS_LEAST] ) >>
qmatch_abbrev_tac `X = Y` >>
qunabbrev_tac`Y` >>
numLib.LEAST_ELIM_TAC >>
rw[Abbr`X`] >- (
  qexists_tac `n` >> rw[] ) >>
numLib.LEAST_ELIM_TAC >>
rw[] >- PROVE_TAC[] >>
qmatch_rename_tac `a = b`[] >>
Cases_on`b < a` >- PROVE_TAC[] >>
Cases_on`a < b` >- (
  res_tac >> DECIDE_TAC ) >>
DECIDE_TAC)

val ALOOKUP_ALL_DISTINCT_MEM = store_thm(
"ALOOKUP_ALL_DISTINCT_MEM",
``ALL_DISTINCT (MAP FST al) ∧ MEM (k,v) al ⇒
  (ALOOKUP al k = SOME v)``,
rw[ALOOKUP_LEAST_EL] >- (
  rw[MEM_MAP,pairTheory.EXISTS_PROD] >>
  PROVE_TAC[]) >>
fs[MEM_EL] >>
pop_assum (assume_tac o SYM) >>
qho_match_abbrev_tac `EL ($LEAST P) (MAP SND al) = v` >>
`P n` by (
  unabbrev_all_tac >> rw[EL_MAP] ) >>
qspecl_then [`P`,`n`] mp_tac LEAST_BOUND >> rw[] >>
numLib.LEAST_ELIM_TAC >>
conj_tac >- (
  qexists_tac `n` >> rw[] ) >>
rw[] >>
qmatch_rename_tac `EL m (MAP SND al) = v`[] >>
`m < LENGTH al` by DECIDE_TAC >>
fs[EL_ALL_DISTINCT_EL_EQ] >>
unabbrev_all_tac >> fs[] >>
`m = n` by PROVE_TAC[] >>
fs[EL_MAP])

val FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM = store_thm(
"FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM",
``!P ls k v fm. ALL_DISTINCT (MAP FST ls) ∧
  MEM (k,v) ls ∧
  P v ⇒
  P ((fm |++ ls) ' k)``,
rw[] >>
ho_match_mp_tac FUPDATE_LIST_APPLY_HO_THM >>
disj1_tac >>
fs[EL_ALL_DISTINCT_EL_EQ,MEM_EL] >>
qpat_assum `(k,v) = X` (assume_tac o SYM) >>
qexists_tac `n` >> rw[EL_MAP] >>
first_x_assum (qspecl_then [`n`,`m`] mp_tac) >>
rw[EL_MAP] >> spose_not_then strip_assume_tac >>
rw[] >> fs[])

val Cevaluate_FUPDATE_Rerr = save_thm(
"Cevaluate_FUPDATE_Rerr",
Cevaluate_FUPDATE
|> Q.SPECL[`env`,`exp`,`Rerr err`]
|> SIMP_RULE (srw_ss()) []
|> Q.GEN`err` |> Q.GEN`exp` |> Q.GEN`env`)

val remove_mat_con_FOLDR = store_thm(
"remove_mat_con_FOLDR",
``∀ps n fk sk v.
  remove_mat_con fk sk v n ps =
    FOLDR (λ(n,p) r.
      let v' = fresh_var ({v;fk} ∪ free_vars sk ∪ Cpat_vars p) in
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

val DROP_NIL = store_thm(
"DROP_NIL",
``∀ls n. (DROP n ls = []) = (n ≥ LENGTH ls)``,
Induct >> rw[] >>
srw_tac[ARITH_ss][])

val (Cpmatch_rules,Cpmatch_ind,Cpmatch_cases) = Hol_reln`
  (Cpmatch (CPvar x) v (FEMPTY |+ (x,v))) ∧
  (Cpmatch (CPlit l) (CLitv l) FEMPTY) ∧
  (Cpmatch_list ps vs env
   ⇒ Cpmatch (CPcon n ps) (CConv n vs) env) ∧
  (Cpmatch_list [] [] FEMPTY) ∧
  (Cpmatch p v env ∧ Cpmatch_list ps vs envs
    ⇒ Cpmatch_list (p::ps) (v::vs) (envs ⊌ env))`

val (Cpnomatch_rules,Cpnomatch_ind,Cpnomatch_cases) = Hol_reln`
  (l ≠ l' ⇒ Cpnomatch (CPlit l) (CLitv l')) ∧
  (Cpnomatch (CPlit l) (CConv c vs)) ∧
  (Cpnomatch (CPlit l) (CRecClos env ns defs n)) ∧
  (Cpnomatch (CPcon c ps) (CLitv l)) ∧
  (c ≠ c' ⇒ Cpnomatch (CPcon c ps) (CConv c' vs)) ∧
  (Cpnomatch_list ps vs ⇒
   Cpnomatch (CPcon c ps) (CConv c vs)) ∧
  (Cpnomatch (CPcon c ps) (CRecClos env ns defs n)) ∧
  (Cpnomatch_list (p::ps) []) ∧
  (Cpnomatch_list [] (v::vs)) ∧
  (Cpnomatch p v ⇒ Cpnomatch_list (p::ps) (v::vs)) ∧
  (Cpnomatch_list ps vs ⇒ Cpnomatch_list (p::ps) (v::vs))`

val Cpmatch_NOT_Cpnomatch = store_thm("Cpmatch_NOT_Cpnomatch",
  ``(∀p v env. Cpmatch p v env ⇒ ¬Cpnomatch p v) ∧
    (∀ps vs env. Cpmatch_list ps vs env ⇒ ¬Cpnomatch_list ps vs)``,
  ho_match_mp_tac Cpmatch_ind >>
  strip_tac >- rw[Once Cpnomatch_cases] >>
  strip_tac >- rw[Once Cpnomatch_cases] >>
  strip_tac >- ( rw[] >> rw[Once Cpnomatch_cases] ) >>
  strip_tac >- rw[Once Cpnomatch_cases] >>
  rw[] >> rw[Once Cpnomatch_cases])

val Cpmatch_or_Cpnomatch = store_thm("Cpmatch_or_Cpnomatch",
  ``(∀p v. (∃env. Cpmatch p v env) ∨ Cpnomatch p v) ∧
    (∀ps vs.  (∃env. Cpmatch_list ps vs env) ∨ Cpnomatch_list ps vs)``,
  ho_match_mp_tac(TypeBase.induction_of``:Cpat``) >>
  strip_tac >- rw[Once Cpmatch_cases] >>
  strip_tac >- (
    rw[Once Cpmatch_cases] >>
    rw[Once Cpnomatch_cases] >>
    Cases_on `v` >> rw[] >> PROVE_TAC[] ) >>
  strip_tac >- (
    rw[] >>
    rw[Once Cpmatch_cases] >>
    rw[Once Cpnomatch_cases] >>
    Cases_on `v` >> rw[] >>
    Cases_on `m=n` >> rw[]  ) >>
  strip_tac >- (
    rw[Once Cpmatch_cases] >>
    rw[Once Cpnomatch_cases] >>
    Cases_on `vs` >> rw[] >> PROVE_TAC[] ) >>
  rw[] >>
  rw[Once Cpmatch_cases] >>
  rw[Once Cpnomatch_cases] >>
  Cases_on `vs` >> rw[] >> PROVE_TAC[] )

val Cpnomatch_thm = store_thm("Cpnomatch_thm",
  ``(Cpnomatch p v = ∀env. ¬Cpmatch p v env) ∧
    (Cpnomatch_list ps vs = ∀env. ¬Cpmatch_list ps vs env)``,
  metis_tac[Cpmatch_NOT_Cpnomatch,Cpmatch_or_Cpnomatch])

val Cpmatch_determ = store_thm("Cpmatch_determ",
  ``(∀p v env. Cpmatch p v env ⇒ ∀env'. Cpmatch p v env' ⇒ (env' = env)) ∧
    (∀ps vs env. Cpmatch_list ps vs env ⇒ ∀env'. Cpmatch_list ps vs env' ⇒ (env' = env))``,
  ho_match_mp_tac Cpmatch_ind >>
  strip_tac >- rw[Once Cpmatch_cases] >>
  strip_tac >- rw[Once Cpmatch_cases] >>
  strip_tac >- (
    rw[] >>
    first_x_assum match_mp_tac >>
    fs[Once Cpmatch_cases] ) >>
  strip_tac >- rw[Once Cpmatch_cases] >>
  rw[] >>
  pop_assum mp_tac >>
  rw[Once Cpmatch_cases] >>
  PROVE_TAC[])

val (Cevaluate_match_rules,Cevaluate_match_ind,Cevaluate_match_cases) = Hol_reln`
  (Cevaluate_match v [] FEMPTY NONE) ∧
  (Cpmatch p v env
    ⇒ Cevaluate_match v ((p,e)::pes) env (SOME e)) ∧
  (Cpnomatch p v ∧ Cevaluate_match v pes env r
    ⇒ Cevaluate_match v ((p,e)::pes) env r)`

val EVERY2_MAP = store_thm("EVERY2_MAP",
  ``(EVERY2 P (MAP f l1) l2 = EVERY2 (λx y. P (f x) y) l1 l2) ∧
    (EVERY2 Q l1 (MAP g l2) = EVERY2 (λx y. Q x (g y)) l1 l2)``,
  rw[EVERY2_EVERY] >>
  Cases_on `LENGTH l1 = LENGTH l2` >> fs[] >>
  rw[ZIP_MAP,EVERY_MEM,MEM_MAP] >>
  srw_tac[DNF_ss][pairTheory.FORALL_PROD] >>
  PROVE_TAC[])

val pmatch_Cpmatch = store_thm("pmatch_Cpmatch",
  ``(∀cenv p v env env'. (pmatch cenv p v env = Match (env' ++ env))
      ⇒ ∀m. Cpmatch (SND (pat_to_Cpat m [] p)) (v_to_Cv m v)
              (alist_to_fmap (env_to_Cenv m env'))) ∧
    (∀cenv ps vs env env'. (pmatch_list cenv ps vs env = Match (env' ++ env))
      ⇒ ∀m. Cpmatch_list (SND (pats_to_Cpats m [] ps)) (vs_to_Cvs m vs)
              (alist_to_fmap (env_to_Cenv m env')))``,
  ho_match_mp_tac pmatch_ind >>
  strip_tac >- (
    rw[pmatch_def,bind_def,
       pat_to_Cpat_def,Once Cpmatch_cases,
       env_to_Cenv_MAP,alist_to_fmap_MAP_values,
       alist_to_fmap_def] >> rw[] ) >>
  strip_tac >- (
    rw[pat_to_Cpat_def,Once Cpmatch_cases,v_to_Cv_def,
       pmatch_def,env_to_Cenv_MAP] >> rw[] ) >>
  strip_tac >- (
    fs[pmatch_def] >>
    rpt gen_tac >> strip_tac >>
    Cases_on `ALOOKUP cenv n` >> fs[] >>
    qmatch_assum_rename_tac `ALOOKUP cenv n = SOME p`[] >>
    PairCases_on `p` >> fs[] >>
    Cases_on `ALOOKUP cenv n'` >> fs[] >>
    qmatch_assum_rename_tac `ALOOKUP cenv n' = SOME p`[] >>
    PairCases_on `p` >> fs[] >>
    rw[] >>
    pop_assum mp_tac >> rw[] >>
    rw[pat_to_Cpat_def] >> rw[v_to_Cv_def] >>
    rw[Once Cpmatch_cases] >>
    first_x_assum (qspec_then `m` mp_tac) >> rw[] ) >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- (
    rw[pmatch_def,env_to_Cenv_MAP,pat_to_Cpat_def,vs_to_Cvs_MAP] >>
    rw[Once Cpmatch_cases] ) >>
  strip_tac >- (
    rw[pmatch_def] >>
    pop_assum mp_tac >>
    fs[Once pmatch_nil] >>
    rw[Once (CONJUNCT1 pmatch_nil)] >>
    Cases_on `pmatch cenv p v []` >> fs[] >> rw[] >>
    qmatch_assum_rename_tac `pmatch cenv p v [] = Match env0`[] >>
    Cases_on `pmatch_list cenv ps vs []` >> fs[] >> rw[] >>
    qmatch_assum_rename_tac `pmatch_list cenv ps vs [] = Match env1`[] >>
    fs[Once (Q.INST[`env`|->`env0++env`]pmatch_nil)] >>
    rpt (first_x_assum (qspec_then `m` mp_tac)) >> rw[] >>
    rw[Once Cpmatch_cases] >>
    rw[pat_to_Cpat_def,vs_to_Cvs_MAP] >>
    qabbrev_tac `Cps = pats_to_Cpats m [] ps` >>
    PairCases_on `Cps` >> fs[] >>
    qabbrev_tac `Cp = pat_to_Cpat m Cps0 p` >>
    PairCases_on `Cp` >> fs[] >>
    fs[Once pat_to_Cpat_empty_pvs] >>
    fs[markerTheory.Abbrev_def] >> rw[] >>
    fs[env_to_Cenv_MAP,vs_to_Cvs_MAP] >>
    PROVE_TAC[] ) >>
  strip_tac >- rw[pmatch_def] >>
  rw[pmatch_def])

val good_cenv_def = Define`
  good_cenv cenv =
  ∀c n s. (MEM (c,(n,s)) cenv) ⇒
    c ∈ s ∧
    ∀c' n' s'. MEM (c',(n',s')) cenv ∧ c' ∈ s' ⇒ (s = s')`

val good_cmap_def = Define`
  good_cmap cenv m =
    ∀c1 n1 c2 n2 s.
      MEM (c1,(n1,s)) cenv ∧
      MEM (c2,(n2,s)) cenv ∧
      (FAPPLY m c1 = FAPPLY m c2) ⇒ (c1 = c2)`

val pmatch_Cpnomatch = store_thm("pmatch_Cpnomatch",
  ``(∀cenv p v env. good_cenv cenv ∧ (pmatch cenv p v env = No_match)
      ⇒ ∀m. good_cmap cenv m ⇒
            Cpnomatch (SND (pat_to_Cpat m [] p)) (v_to_Cv m v)) ∧
    (∀cenv ps vs env env'. good_cenv cenv ∧ (pmatch_list cenv ps vs env = No_match)
      ⇒ ∀m. good_cmap cenv m ⇒
            Cpnomatch_list (SND (pats_to_Cpats m [] ps)) (vs_to_Cvs m vs))``,
  ho_match_mp_tac pmatch_ind >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- (
    rw[pmatch_def,lit_same_type_def] >>
    pop_assum mp_tac >> BasicProvers.EVERY_CASE_TAC >>
    rw[pat_to_Cpat_def,Once Cpnomatch_cases,v_to_Cv_def] ) >>
  strip_tac >- (
    fs[pmatch_def] >>
    rpt gen_tac >> strip_tac >>
    Cases_on `ALOOKUP cenv n` >> fs[] >>
    qmatch_assum_rename_tac `ALOOKUP cenv n = SOME p`[] >>
    PairCases_on `p` >> fs[] >>
    Cases_on `ALOOKUP cenv n'` >> fs[] >>
    qmatch_assum_rename_tac `ALOOKUP cenv n' = SOME p`[] >>
    PairCases_on `p` >> fs[] >>
    rw[] >>
    pop_assum mp_tac >> rw[] >>
    rw[pat_to_Cpat_def] >> rw[v_to_Cv_def] >>
    rw[Once Cpnomatch_cases]
      >- PROVE_TAC[pairTheory.SND] >>
    fs[good_cenv_def,good_cmap_def] >>
    imp_res_tac ALOOKUP_MEM >>
    PROVE_TAC[] ) >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- (
    rw[pmatch_def] >>
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    fs[Once pmatch_nil] >>
    rw[Once (CONJUNCT1 pmatch_nil)] >>
    Cases_on `pmatch cenv p v []` >> fs[] >> rw[] >- (
      rw[pat_to_Cpat_def,vs_to_Cvs_MAP] >>
      rw[Once Cpnomatch_cases] >>
      fs[Once pat_to_Cpat_empty_pvs] >>
      PROVE_TAC[] ) >>
    rw[pat_to_Cpat_def,vs_to_Cvs_MAP] >>
    rw[Once Cpnomatch_cases] >>
    fs[Once pat_to_Cpat_empty_pvs] >>
    fs[vs_to_Cvs_MAP] >> rw[] >>
    disj2_tac >> first_x_assum (match_mp_tac o MP_CANON) >>
    rw[Once pmatch_nil] ) >>
  strip_tac >- rw[pmatch_def] >>
  rw[pmatch_def])

val matchres_def = Define`
  matchres env cenv env' e r = ∃env''. (env' = env'' ++ env) ∧ (r = Rval (env'',e))`

val evaluate_match_with_Cevaluate_match = store_thm("evaluate_match_with_Cevaluate_match",
  ``∀pes r. evaluate_match_with (matchres env) cenv env v pes r ⇒
      ∀m. good_cenv cenv ∧ good_cmap cenv m ⇒
        ((r = Rerr (Rraise Bind_error))
            ⇒ Cevaluate_match (v_to_Cv m v)
                (MAP (λ(p,e). (SND (pat_to_Cpat m [] p),e)) pes)
                FEMPTY NONE) ∧
        ∀env' e. (r = Rval (env',e))
          ⇒ Cevaluate_match (v_to_Cv m v)
              (MAP (λ(p,e). (SND (pat_to_Cpat m [] p),e)) pes)
              (alist_to_fmap (env_to_Cenv m env')) (SOME e)``,
  ho_match_mp_tac evaluate_match_with_ind >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_match_cases] ) >>
  strip_tac >- (
    rw[] >> rw[Once Cevaluate_match_cases] >>
    fs[matchres_def] >>
    PROVE_TAC[pmatch_Cpmatch] ) >>
  strip_tac >- (
    rw[] >>
    rw[Once Cevaluate_match_cases] >>
    PROVE_TAC[pmatch_Cpnomatch] ) >>
  strip_tac >- rw[] >> rw[] )

val evaluate_match_with_matchres = store_thm("evaluate_match_with_matchres",
  ``∀pes r. evaluate_match_with P cenv env v pes r ⇒
            (r ≠ Rerr Rtype_error) ⇒
            ((r = Rerr (Rraise Bind_error)) ∧
             evaluate_match_with (matchres env) cenv env v pes (Rerr (Rraise Bind_error))) ∨
            ∃menv mr. evaluate_match_with (matchres env) cenv env v pes (Rval (menv,mr)) ∧
                      P cenv (menv++env) mr r``,
  ho_match_mp_tac evaluate_match_with_ind >>
  strip_tac >- rw[Once evaluate_match_with_cases] >>
  strip_tac >- (
    rw[] >>
    disj2_tac >>
    rw[Once evaluate_match_with_cases] >>
    rw[matchres_def] >>
    fs[Once pmatch_nil] >>
    Cases_on `pmatch cenv p v []` >>fs[] >>
    PROVE_TAC[] ) >>
  strip_tac >- (
    rw[] >> fs[] >>
    rw[Once evaluate_match_with_cases] >>
    disj2_tac >>
    rw[Once evaluate_match_with_cases] >>
    PROVE_TAC[] ) >>
  strip_tac >- rw[] >>
  rw[])

val evaluate_match_with_matchres_closed = store_thm("evaluate_match_with_matchres_closed",
  ``∀pes r. evaluate_match_with (matchres env) cenv env v pes r ⇒
            EVERY closed (MAP SND env) ∧ closed v ⇒
            every_result (λ(menv,mr). EVERY closed (MAP SND menv) ∧
                                      ∃p. MEM (p,mr) pes ∧
                                          (set (MAP FST menv) = pat_vars p)) r ``,
  ho_match_mp_tac evaluate_match_with_ind >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[matchres_def] >>
    fs[] >>
    fs[Once pmatch_nil] >>
    Cases_on `pmatch cenv p v []` >> fs[] >>
    qspecl_then [`cenv`,`p`,`v`,`[]`] mp_tac (CONJUNCT1 pmatch_closed) >>
    fs[] >> fsrw_tac[DNF_ss][] ) >>
  strip_tac >- (
    rw[] >> fs[] >>
    Cases_on `r` >> fs[] >>
    fs[pairTheory.UNCURRY] >>
    fsrw_tac[DNF_ss][] >> PROVE_TAC[]) >>
  strip_tac >- rw[] >>
  rw[])

val Cevaluate_match_MAP_exp = store_thm("Cevaluate_match_MAP_exp",
  ``∀pes env r. Cevaluate_match v pes env r ⇒
      ∀f. Cevaluate_match v (MAP (λ(p,e). (p, f e)) pes) env (OPTION_MAP f r)``,
  ho_match_mp_tac Cevaluate_match_ind >>
  strip_tac >- rw[Once Cevaluate_match_rules] >>
  strip_tac >- rw[Once Cevaluate_match_cases] >>
  rw[] >>
  rw[Once Cevaluate_match_cases])

val Cpmatch_list_LENGTH = store_thm("Cpmatch_list_LENGTH",
  ``∀ps vs menv. Cpmatch_list ps vs menv ⇒ (LENGTH ps = LENGTH vs)``,
  Induct >> rw[Once Cpmatch_cases] >> rw[] >> PROVE_TAC[])

val Cpmatch_list_nil = store_thm("Cpmatch_list_nil",
  ``(Cpmatch_list [] vs e = ((vs = []) ∧ (e = FEMPTY))) ∧
    (Cpmatch_list ps [] e = ((ps = []) ∧ (e = FEMPTY)))``,
  rw[Once Cpmatch_cases] >>
  rw[Once Cpmatch_cases] )
val _ = export_rewrites["Cpmatch_list_nil"]

val Cpmatch_list_APPEND = store_thm("Cpmatch_list_APPEND",
  ``∀p0 p1 vs e. Cpmatch_list (p0 ++ p1) vs e =
            ∃e0 e1. Cpmatch_list p0 (TAKE (LENGTH p0) vs) e0 ∧
                    Cpmatch_list p1 (DROP (LENGTH p0) vs) e1 ∧
                    (e = e1 ⊌ e0)``,
  Induct >- (
    rw[Once Cpmatch_cases] >>
    rw[FUNION_FEMPTY_2] >>
    Cases_on `p1` >> fs[] >>
    rw[Once Cpmatch_cases,SimpRHS] ) >>
  rw[Once Cpmatch_cases] >>
  Cases_on `vs` >> fs[] >>
  rw[Once Cpmatch_cases,SimpRHS] >>
  srw_tac[DNF_ss][FUNION_ASSOC] >>
  PROVE_TAC[])

val Cpmatch_FDOM = store_thm("Cpmatch_FDOM",
  ``(∀p v env. Cpmatch p v env ⇒ (FDOM env = Cpat_vars p)) ∧
    (∀ps vs env. Cpmatch_list ps vs env ⇒ (FDOM env = BIGUNION (IMAGE Cpat_vars (set ps))))``,
  ho_match_mp_tac Cpmatch_ind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[FOLDL_UNION_BIGUNION] >>
  strip_tac >- rw[] >>
  rw[UNION_COMM])

val Cpmatch_closed = store_thm("Cpmatch_closed",
  ``(∀p v e. Cpmatch p v e ⇒ Cclosed v ⇒ ∀v. v ∈ FRANGE e ⇒ Cclosed v) ∧
    (∀ps vs e. Cpmatch_list ps vs e ⇒ EVERY Cclosed vs ⇒ ∀v. v ∈ FRANGE e ⇒ Cclosed v)``,
  ho_match_mp_tac Cpmatch_ind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (rw[] >> fs[Once Cclosed_cases]) >>
  rw[] >>
  fsrw_tac[DNF_ss][FRANGE_DEF,FUNION_DEF] >>
  rw[])

val Cpmatch_strongind = theorem"Cpmatch_strongind"

val Cpmatch_remove_mat = store_thm("Cpmatch_remove_mat",
  ``(∀p v menv. Cpmatch p v menv ⇒
       ∀env x fk e r0.
         (FLOOKUP env x = SOME v) ∧ fk ∈ FDOM env ∧ x ∉ Cpat_vars p ∧
         Cclosed v ∧ (∀v. v ∈ FRANGE env ⇒ Cclosed v) ∧
         free_vars e ⊆ Cpat_vars p ∪ FDOM env ∧
         Cevaluate (menv ⊌ env) e r0
       ⇒ ∃r. Cevaluate env (remove_mat_vp fk e x p) r ∧
             result_rel syneq r r0) ∧
    (∀ps vs menv. Cpmatch_list ps vs menv ⇒
       ∀env x c vs0 ps0 menv0 fk e r0.
         (FLOOKUP env x = SOME (CConv c (vs0++vs))) ∧
         fk ∈ FDOM env ∧
         x ∉ BIGUNION (IMAGE Cpat_vars (set (ps0++ps))) ∧
         EVERY Cclosed (vs0++vs) ∧ (∀v. v ∈ FRANGE env ⇒ Cclosed v) ∧
         free_vars e ⊆ BIGUNION (IMAGE Cpat_vars (set (ps0++ps))) ∪ FDOM env ∧
         Cpmatch_list ps0 vs0 menv0 ∧
         Cevaluate (menv ⊌ menv0 ⊌ env) e r0
       ⇒ ∃r. Cevaluate (menv0 ⊌ env) (remove_mat_con fk e x (LENGTH ps0) ps) r ∧
             result_rel syneq r r0)``,
  ho_match_mp_tac Cpmatch_strongind >>
  strip_tac >- (
    rw[remove_mat_var_def] >>
    rw[Once Cevaluate_cases] >>
    fs[FLOOKUP_DEF] >>
    fs[FUNION_FUPDATE_1,FUNION_FEMPTY_1] >>
    PROVE_TAC[result_rel_refl,syneq_refl]) >>
  strip_tac >- (
    rw[remove_mat_vp_def] >>
    fs[FLOOKUP_DEF] >>
    rw[Once Cevaluate_cases] >>
    srw_tac[DNF_ss][] >>
    disj1_tac >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `T` >>
    fs[FUNION_FEMPTY_1] >>
    rw[Once Cevaluate_cases] >>
    rw[Cevaluate_list_with_Cevaluate,Cevaluate_list_with_cons] >>
    PROVE_TAC[result_rel_refl,syneq_refl]) >>
  strip_tac >- (
    rw[] >>
    rw[Once Cevaluate_cases] >>
    srw_tac[DNF_ss][] >>
    disj1_tac >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `T` >>
    fs[] >>
    fs[RIGHT_EXISTS_AND_THM,GSYM CONJ_ASSOC] >>
    conj_tac >- (
      rw[Once Cevaluate_cases] >>
      fs[FLOOKUP_DEF] ) >>
    `0 = LENGTH ([]:Cpat list)` by rw[] >> pop_assum SUBST1_TAC >>
    `env = FEMPTY ⊌ env` by rw[FUNION_FEMPTY_1] >> pop_assum SUBST1_TAC >>
    first_x_assum (match_mp_tac o MP_CANON) >>
    fs[FOLDL_UNION_BIGUNION] >>
    rw[FUNION_FEMPTY_2] >>
    fs[Once Cclosed_cases]) >>
  strip_tac >- (
    rw[FUNION_FEMPTY_1] >>
    PROVE_TAC[result_rel_refl,syneq_refl] ) >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  rw[LET_THM] >>
  rw[Once Cevaluate_cases] >>
  srw_tac[DNF_ss][] >>
  disj1_tac >>
  rw[Once Cevaluate_cases] >>
  srw_tac[DNF_ss][] >>
  disj2_tac >>
  map_every (fn q => CONV_TAC SWAP_EXISTS_CONV >> qexists_tac q) [`c`,`vs0++v::vs`] >>
  `x ∈ FDOM env` by fs[FLOOKUP_DEF] >>
  `LENGTH ps0 = LENGTH vs0` by imp_res_tac Cpmatch_list_LENGTH >>
  fs[] >>
  fs[RIGHT_EXISTS_AND_THM,GSYM CONJ_ASSOC] >>
  conj_tac >- (
    imp_res_tac Cpmatch_FDOM >>
    fsrw_tac[DNF_ss][FUNION_DEF] >>
    rw[] >> fs[FLOOKUP_DEF] >>
    PROVE_TAC[] ) >>
  fs[rich_listTheory.EL_LENGTH_APPEND] >>
  first_x_assum (qspecl_then [`env`,`x`,`c`,`vs0 ++ [v]`,`ps0++[p]`,`menv ⊌ menv0`,`fk`,`e`,`r0`] mp_tac) >>
  fs[] >>
  fs[FUNION_ASSOC] >>
  fs[Cpmatch_list_APPEND] >>
  fs[rich_listTheory.FIRSTN_LENGTH_APPEND] >>
  fs[rich_listTheory.BUTFIRSTN_LENGTH_APPEND] >>
  simp_tac(srw_ss())[Q.SPEC`[p]`(CONJUNCT2 Cpmatch_cases)] >>
  fsrw_tac[DNF_ss][] >>
  fs[FUNION_FEMPTY_1] >>
  fsrw_tac[DNF_ss][CONJ_ASSOC] >>
  qho_match_abbrev_tac `(∀x y. P x y ⇒ Q x y) ⇒ R` >>
  strip_tac >>
  `Q menv0 menv` by (
    pop_assum match_mp_tac >>
    unabbrev_all_tac >>
    rw[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    PROVE_TAC[] ) >>
  pop_assum mp_tac >> pop_assum kall_tac >>
  unabbrev_all_tac >> rw[] >>
  qmatch_abbrev_tac `∃r. Cevaluate env' (remove_mat_vp fk e' x' p) r ∧ result_rel syneq r r0` >>
  first_x_assum (qspecl_then [`env'`,`x'`,`fk`,`e'`] mp_tac) >>
  fs[FLOOKUP_DEF,Abbr`env'`] >>
  `x' ∉ Cpat_vars p` by (
    unabbrev_all_tac >>
    match_mp_tac fresh_var_not_in_any >>
    rw[] ) >>
  `x' ∉ FDOM menv` by metis_tac[Cpmatch_FDOM] >>
  fs[FUNION_FUPDATE_2,FUNION_ASSOC] >>
  fs[GSYM AND_IMP_INTRO] >>
  fs[RIGHT_FORALL_IMP_THM] >>
  qmatch_abbrev_tac `(P ⇒ Q) ⇒ R` >>
  `P` by (
    unabbrev_all_tac >>
    fsrw_tac[DNF_ss][] >>
    match_mp_tac IN_FRANGE_DOMSUB_suff >>
    match_mp_tac IN_FRANGE_FUNION_suff >>
    fs[] >>
    imp_res_tac Cpmatch_closed ) >>
  fs[] >> pop_assum kall_tac >>
  unabbrev_all_tac >>
  qmatch_abbrev_tac `(P ⇒ Q) ⇒ R` >>
  `P` by (
    unabbrev_all_tac >>
    qspecl_then [`ps`,`fk`,`e`,`x`,`LENGTH vs0 + 1`] mp_tac
      (CONJUNCT2 free_vars_remove_mat_vp_SUBSET) >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    imp_res_tac Cpmatch_FDOM >>
    fsrw_tac[DNF_ss][] >>
    metis_tac[] ) >>
  fs[] >> pop_assum kall_tac >>
  unabbrev_all_tac >>
  qho_match_abbrev_tac `(∀r. P r ⇒ Q r) ⇒ R` >>
  qsuff_tac `∃rx. P rx ∧ result_rel syneq r rx` >- (
    rw[] >>
    `Q rx` by metis_tac[] >>
    unabbrev_all_tac >>
    fs[] >>
    metis_tac[result_rel_syneq_trans,result_rel_syneq_sym]) >>
  unabbrev_all_tac >>
  rw[] >>
  match_mp_tac Cevaluate_FUPDATE >>
  fs[] >>
  imp_res_tac Cpmatch_FDOM >>
  qspecl_then [`ps`,`fk`,`e`,`x`,`LENGTH vs0 + 1`] mp_tac
    (CONJUNCT2 free_vars_remove_mat_vp_SUBSET) >>
  strip_tac >>
  fsrw_tac[DNF_ss][SUBSET_DEF] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (
    match_mp_tac IN_FRANGE_FUNION_suff >> fs[] >>
    imp_res_tac Cpmatch_closed >> fs[] >>
    match_mp_tac IN_FRANGE_FUNION_suff >> fs[] ) >>
  match_mp_tac fresh_var_not_in_any >>
  fsrw_tac[DNF_ss][SUBSET_DEF] >>
  metis_tac[])

val Cpnomatch_strongind = theorem"Cpnomatch_strongind"

val Cpnomatch_remove_mat = store_thm("Cpnomatch_remove_mat",
  ``(∀p v. Cpnomatch p v ⇒
       ∀env x fk e r0.
         (FLOOKUP env x = SOME v) ∧
         Cevaluate env (CCall (CVar fk) []) r0
         ⇒ ∃r. Cevaluate env (remove_mat_vp fk e x p) r ∧
               ((r = Rerr Rtype_error) ∨ (r = r0))) ∧
    (∀ps vs. Cpnomatch_list ps vs ⇒
       ∀env x c vs0 ps0 fk e r0.
         (FLOOKUP env x = SOME (CConv c (vs0 ++ vs))) ∧
         Cevaluate env (CCall (CVar fk) []) r0
         ⇒ ∃r. Cevaluate env (remove_mat_con fk e x (LENGTH ps0) ps) r ∧
               ((r = Rerr Rtype_error) ∨ (r = r0)))``,
  ho_match_mp_tac Cpnomatch_ind >>
  strip_tac >- (
    rw[] >>
    rw[Once Cevaluate_cases] >>
    srw_tac[DNF_ss][] >>
    disj1_tac >> disj2_tac >>
    qexists_tac `F` >> fs[] >>
    rw[Once Cevaluate_cases] >>
    fs[FLOOKUP_DEF] >>
    rw[Cevaluate_list_with_Cevaluate,Cevaluate_list_with_cons] ) >>
  strip_tac >- (
    rw[] >>
    rw[Once Cevaluate_cases] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    fs[FLOOKUP_DEF] >>
    rw[Cevaluate_list_with_Cevaluate,Cevaluate_list_with_cons] >>
    rw[Once Cevaluate_cases] >>
    rw[Cevaluate_list_with_Cevaluate,Cevaluate_list_with_cons] ) >>
  strip_tac >- (
    rw[FLOOKUP_DEF] >>
    rw[Once Cevaluate_cases] >>
    rw[Once Cevaluate_cases] >>
    rw[Cevaluate_list_with_Cevaluate,Cevaluate_list_with_cons] >>
    rw[Once Cevaluate_cases] >>
    rw[Cevaluate_list_with_Cevaluate,Cevaluate_list_with_cons] ) >>
  strip_tac >- (
    rw[FLOOKUP_DEF] >>
    rw[Once Cevaluate_cases] >>
    rw[Once Cevaluate_cases] >>
    rw[Cevaluate_list_with_Cevaluate,Cevaluate_list_with_cons] >>
    rw[Once Cevaluate_cases] >>
    rw[Cevaluate_list_with_Cevaluate,Cevaluate_list_with_cons] ) >>
  strip_tac >- (
    rw[FLOOKUP_DEF] >>
    rw[Once Cevaluate_cases] >>
    rw[Once Cevaluate_cases] >>
    PROVE_TAC[] ) >>
  strip_tac >- (
    rw[FLOOKUP_DEF] >>
    rw[Once Cevaluate_cases] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    `env ' x = CConv c ([] ++ vs)` by rw[] >>
    res_tac >>
    metis_tac[LENGTH_NIL] ) >>
  strip_tac >- (
    rw[FLOOKUP_DEF] >>
    rw[Once Cevaluate_cases] >>
    rw[Once Cevaluate_cases] >>
    rw[Once Cevaluate_cases] ) >>
  strip_tac >- (
    rw[FLOOKUP_DEF] >>
    rw[Once Cevaluate_cases] >>
    rw[Once Cevaluate_cases] >>
    rw[Cevaluate_proj] >>
    Cases_on `LENGTH ps0 < LENGTH vs0` >> fs[]

(* TODO: Is Cpes_vars necessary, or is Cpat_vars enough? *)

val Cevaluate_match_strongind = theorem"Cevaluate_match_strongind"

val Cevaluate_match_remove_mat_var = store_thm("Cevaluate_match_remove_mat_var",
  ``∀pes menv mr. Cevaluate_match v pes menv mr ⇒
      ∀env x. (FLOOKUP env x = SOME v) ∧
              x ∉ BIGUNION (IMAGE (Cpat_vars o FST) (set pes)) ∧
              BIGUNION (IMAGE (λ(p,e). free_vars e DIFF Cpat_vars p) (set pes)) ⊆ FDOM env ∧
              Cclosed v ∧
              (∀v. v ∈ FRANGE env ⇒ Cclosed v) ⇒
       case mr of
       | NONE => Cevaluate env (remove_mat_var x pes) (Rerr (Rraise Bind_error))
       | SOME e => ∀r0. Cevaluate (menv ⊌ env) e r0
                  ⇒ ∃r. Cevaluate env (remove_mat_var x pes) r ∧
                        result_rel syneq r r0``,
  ho_match_mp_tac Cevaluate_match_ind >>
  strip_tac >- rw[remove_mat_var_def] >>
  strip_tac >- (
    rw[remove_mat_var_def,LET_THM] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    CONV_TAC SWAP_EXISTS_CONV >>
    Q.PAT_ABBREV_TAC`fk = fresh_var X` >>
    qexists_tac `fresh_var (free_vars (remove_mat_vp fk e x p))` >>
    rw[RIGHT_EXISTS_AND_THM,GSYM CONJ_ASSOC]
      >- rw[fresh_var_not_in,FINITE_has_fresh_string] >>
    qmatch_abbrev_tac `∃r. Cevaluate ee (remove_mat_vp fk e x p) r ∧ result_rel syneq r r0` >>
    qspecl_then [`p`,`v`,`menv`] mp_tac (CONJUNCT1 Cpmatch_remove_mat) >>
    fs[] >>
    disch_then (qspecl_then [`ee`,`x`,`fk`,`e`] mp_tac) >>
    fsrw_tac[DNF_ss][pairTheory.FORALL_PROD] >>
    `fk ∉ {x} ∪ free_vars e` by (
      rw[Abbr`fk`,fresh_var_not_in,FINITE_has_fresh_string] ) >>
    `FLOOKUP ee x = SOME v` by fs[Abbr`ee`,FLOOKUP_UPDATE] >> fs[] >>
    `fk ∈ FDOM ee` by fs[Abbr`ee`] >> fs[] >>
    `x ∉ Cpat_vars p` by metis_tac[] >> fs[] >>
    `∀v. v ∈ FRANGE ee ⇒ Cclosed v` by (
      unabbrev_all_tac >>
      match_mp_tac IN_FRANGE_FUPDATE_suff  >>
      fs[] >>
      rw[Once Cclosed_cases] >>
      qspecl_then [`x`,`pes`] strip_assume_tac free_vars_remove_mat_var >>
      pop_assum mp_tac >>
      srw_tac[DNF_ss][Once EXTENSION,SUBSET_DEF] >>
      fsrw_tac[DNF_ss][pairTheory.EXISTS_PROD,SUBSET_DEF] >>
      `x ∈ FDOM env` by fs[FLOOKUP_DEF] >>
      fsrw_tac[DNF_ss][pairTheory.FORALL_PROD] >>
      metis_tac[] ) >> fs[] >>
    `free_vars e ⊆ Cpat_vars p ∪ FDOM ee` by (
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      rw[Abbr`ee`] >>
      metis_tac[] ) >> fs[] >>
    qsuff_tac `∃rx. Cevaluate (menv ⊌ ee) e rx ∧ result_rel syneq r0 rx` >- (
      metis_tac[result_rel_syneq_trans,result_rel_syneq_sym] ) >>
    unabbrev_all_tac >>
    Q.PAT_ABBREV_TAC`fv = fresh_var (free_vars X)` >>
    Q.PAT_ABBREV_TAC`fk = fresh_var (a ∪ b)` >>
    Cases_on `fk ∈ FDOM menv` >>
    rw[FUNION_FUPDATE_2] >- metis_tac[result_rel_refl,syneq_refl] >>
    match_mp_tac (MP_CANON Cevaluate_FUPDATE) >>
    fs[] >>
    imp_res_tac Cpmatch_FDOM >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    conj_tac >- PROVE_TAC[] >>
    match_mp_tac IN_FRANGE_FUNION_suff >>
    fs[] >>
    imp_res_tac Cpmatch_closed) >>
  rw[] >>
  rw[remove_mat_var_def] >>
  Cases_on `mr` >> fs[] >- (
    rw[Once Cevaluate_cases] >>

  Cpnomatch_thm

val exp_to_Cexp_thm1 = store_thm("exp_to_Cexp_thm1",
  ``∀cenv env exp res. evaluate cenv env exp res ⇒
    (EVERY closed (MAP SND env)) ∧ (FV exp ⊆ set (MAP FST env)) ∧
    good_cenv cenv ∧ (res ≠ Rerr Rtype_error) ⇒
    ∀m. good_cmap cenv m ⇒
      ∃Cres. Cevaluate (alist_to_fmap (env_to_Cenv m env)) (exp_to_Cexp m exp) Cres ∧
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
  qpat_assum `good_cmap cenv m` assume_tac >>
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
  qpat_assum `good_cmap cenv m` assume_tac >> fs[] >>
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
    `every_result closed (Rval v1) ∧
     every_result closed (Rval v2)` by metis_tac[evaluate_closed] >>
    fs[] >>
    `EVERY closed (MAP SND env') ∧
     FV exp'' ⊆ set (MAP FST env')` by PROVE_TAC[do_app_closed] >>
    fs[] >>
    rpt (first_x_assum (qspec_then `m` mp_tac)) >> rw[] >>
    qmatch_assum_rename_tac `syneq (v_to_Cv m v1) w1`[] >>
    qmatch_assum_rename_tac `syneq (v_to_Cv m v2) w2`[] >>
    Cases_on `opb` >> fsrw_tac[DNF_ss][]
    >- (
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
      rw[] >> fs[v_to_Cv_def] >> fs[Q.SPEC`CLitv l`syneq_cases])
    >- (
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
      `free_vars exp0 ⊆ FDOM env0` by (
        fs[Abbr`exp0`,Abbr`env0`,env_to_Cenv_MAP,MAP_MAP_o,
           pairTheory.LAMBDA_PROD,combinTheory.o_DEF,FST_pair] ) >>
      `every_result Cclosed (Rval w1)` by (
        match_mp_tac (MP_CANON Cevaluate_closed) >>
        map_every qexists_tac [`env0`,`exp_to_Cexp m e1`] >>
        fs[Abbr`env0`,env_to_Cenv_MAP,MAP_MAP_o,
           pairTheory.LAMBDA_PROD,combinTheory.o_DEF,FST_pair] ) >>
      `∃res. Cevaluate (env0 |+ (fresh_var (FV e2),w1)) exp0 res ∧
             result_rel syneq (Rval w2) res` by (
        match_mp_tac Cevaluate_FUPDATE >>
        fs[Abbr`exp0`] >>
        rw[fresh_var_not_in,FINITE_has_fresh_string] ) >>
      fs[] >> rw[] >>
      qmatch_assum_rename_tac `syneq w2 y2`[] >>
      CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `y2` >> fs[] >>
      rw[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >>
      disj1_tac >>
      rw[Cevaluate_list_with_Cevaluate] >>
      rw[Cevaluate_list_with_cons] >>
      rw[FAPPLY_FUPDATE_THM,NOT_fresh_var] >>
      Cases_on `v1` >> Cases_on `l` >> fs[MiniMLTheory.do_app_def] >>
      Cases_on `v2` >> Cases_on `l` >> fs[] >> rw[] >>
      fs[doPrim2_def,exp_to_Cexp_def,MiniMLTheory.opb_lookup_def] >>
      fs[v_to_Cv_def,Q.SPEC`CLitv l`syneq_cases] >> rw[] >>
      fs[Q.SPEC`CLitv l`syneq_cases] >> rw[] >>
      rw[integerTheory.int_gt,integerTheory.int_ge])
    >- (
      rw[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >>
      disj1_tac >>
      rw[Cevaluate_list_with_Cevaluate] >>
      rw[Cevaluate_list_with_cons] >>
      rw[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >>
      rw[Cevaluate_list_with_Cevaluate] >>
      rw[Cevaluate_list_with_cons] >>
      CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `w1` >>
      CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `w2` >>
      rw[] >>
      Cases_on `v1` >> Cases_on `l` >> fs[MiniMLTheory.do_app_def] >>
      Cases_on `v2` >> Cases_on `l` >> fs[] >> rw[] >>
      fs[CevalPrim2_def,doPrim2_def,exp_to_Cexp_def,MiniMLTheory.opb_lookup_def] >>
      rw[] >> fs[v_to_Cv_def] >> fs[Q.SPEC`CLitv l`syneq_cases] >>
      rw[CompileTheory.i1_def] >> ARITH_TAC)
    >- (
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
      `free_vars exp0 ⊆ FDOM env0` by (
        fs[Abbr`exp0`,Abbr`env0`,env_to_Cenv_MAP,MAP_MAP_o,
           pairTheory.LAMBDA_PROD,combinTheory.o_DEF,FST_pair] ) >>
      `every_result Cclosed (Rval w1)` by (
        match_mp_tac (MP_CANON Cevaluate_closed) >>
        map_every qexists_tac [`env0`,`exp_to_Cexp m e1`] >>
        fs[Abbr`env0`,env_to_Cenv_MAP,MAP_MAP_o,
           pairTheory.LAMBDA_PROD,combinTheory.o_DEF,FST_pair] ) >>
      `∃res. Cevaluate (env0 |+ (fresh_var (FV e2),w1)) exp0 res ∧
             result_rel syneq (Rval w2) res` by (
        match_mp_tac Cevaluate_FUPDATE >>
        fs[Abbr`exp0`] >>
        rw[fresh_var_not_in,FINITE_has_fresh_string] ) >>
      fs[] >> rw[] >>
      qmatch_assum_rename_tac `syneq w2 y2`[] >>
      CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `y2` >> fs[] >>
      rw[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >>
      disj1_tac >>
      rw[Cevaluate_list_with_Cevaluate] >>
      rw[Cevaluate_list_with_cons] >>
      rw[FAPPLY_FUPDATE_THM,NOT_fresh_var] >>
      Cases_on `v1` >> Cases_on `l` >> fs[MiniMLTheory.do_app_def] >>
      Cases_on `v2` >> Cases_on `l` >> fs[] >> rw[] >>
      fs[doPrim2_def,exp_to_Cexp_def,MiniMLTheory.opb_lookup_def] >>
      fs[v_to_Cv_def,Q.SPEC`CLitv l`syneq_cases] >> rw[] >>
      fs[Q.SPEC`CLitv l`syneq_cases] >> rw[] >>
      rw[Once Cevaluate_cases] >>
      rw[Cevaluate_list_with_Cevaluate] >>
      rw[Cevaluate_list_with_cons] >>
      rw[FAPPLY_FUPDATE_THM,NOT_fresh_var] >>
      rw[CompileTheory.i1_def] >>
      ARITH_TAC))
  >- (
    rw[Once Cevaluate_cases] >>
    srw_tac[DNF_ss][] >>
    disj1_tac >>
    rw[Cevaluate_list_with_Cevaluate] >>
    rw[Cevaluate_list_with_cons] >>
    fs[] >>
    rpt (first_x_assum (qspec_then `m` mp_tac)) >>
    rw[] >>
    qmatch_assum_rename_tac `syneq (v_to_Cv m v1) w1`[] >>
    qmatch_assum_rename_tac `syneq (v_to_Cv m v2) w2`[] >>
    qexists_tac `w1` >>
    qexists_tac `w2` >>
    fs[] >>
    fs[MiniMLTheory.do_app_def] >>
    qmatch_abbrev_tac `P` >> rw[] >>
    fs[exp_to_Cexp_def] >> rw[] >>
    fs[v_to_Cv_def] >>
    rw[Abbr`P`,Q.SPEC`CLitv l`syneq_cases] >>
    cheat )
  >- (
    `every_result closed (Rval v1) ∧
     every_result closed (Rval v2)` by (
      conj_tac >>
      match_mp_tac (MP_CANON evaluate_closed) >>
      PROVE_TAC[]) >>
    fs[] >>
    `EVERY closed (MAP SND env') ∧
     FV exp'' ⊆ set (MAP FST env')` by
      metis_tac[do_app_closed] >>
    fs[] >>
    rpt (first_x_assum (qspec_then `m` mp_tac)) >> rw[] >>
    qmatch_assum_rename_tac `syneq (v_to_Cv m v1) w1`[] >>
    qmatch_assum_rename_tac `syneq (v_to_Cv m v2) w2`[] >>
    rw[Once Cevaluate_cases] >>
    srw_tac[DNF_ss][] >>
    disj1_tac >>
    rw[Cevaluate_list_with_Cevaluate] >>
    rw[Cevaluate_list_with_cons] >>
    srw_tac[DNF_ss][] >>
    qmatch_assum_abbrev_tac `Cevaluate env0 ee1 (Rval w1)` >>
    qmatch_assum_abbrev_tac `Cevaluate env0 ee2 (Rval w2)` >>
    `∀v. v ∈ FRANGE env0 ⇒ Cclosed v` by (
      unabbrev_all_tac >>
      match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      fs[env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,
         pairTheory.LAMBDA_PROD] >>
      fs[MEM_MAP,pairTheory.EXISTS_PROD] >>
      srw_tac[DNF_ss][] >>
      match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
      fs[EVERY_MEM,MEM_MAP,pairTheory.EXISTS_PROD] >>
      PROVE_TAC[]) >>
    `every_result Cclosed (Rval w1) ∧
     every_result Cclosed (Rval w2)` by(
       conj_tac >>
       match_mp_tac (MP_CANON Cevaluate_closed) >>
       qexists_tac `alist_to_fmap (env_to_Cenv m env)` >|[
         qexists_tac `exp_to_Cexp m e1`,
         qexists_tac `exp_to_Cexp m e2`] >>
       fs[] >>
       fs[env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,
          pairTheory.LAMBDA_PROD,FST_pair] ) >>
    `∃env1 ns' defs n. w1 = CRecClos env1 ns' defs n` by (
      imp_res_tac do_Opapp_SOME_CRecClos >> rw[] ) >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `env1` >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `ns'` >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `defs` >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `n` >>
    rw[] >>
    fs[Q.SPEC`CRecClos env1 ns' defs n`Cclosed_cases] >>
    fs[MEM_EL] >> rw[] >>
    qabbrev_tac `p = EL n' defs` >>
    PairCases_on `p` >>
    pop_assum (mp_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def]) >>
    rw[] >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `w2` >>
    rw[] >>
    fs[MiniMLTheory.do_app_def] >>
    Cases_on `v1` >> fs[] >- (
      fs[v_to_Cv_def,LET_THM] >>
      fs[Q.SPEC`CRecClos env1 ns' defs zz`syneq_cases] >>
      rw[] >> fs[] >> rw[] >> fs[] >> rw[] >>
      Q.PAT_ABBREV_TAC`env2 = X:string|->Cv` >>
      qmatch_assum_rename_tac `Cevaluate X (exp_to_Cexp m e) r`["X"] >>
      qmatch_assum_abbrev_tac`Cevaluate env3 ee r` >>
      qspecl_then [`env3`,`ee`,`r`] mp_tac Cevaluate_free_vars_env >>
      `free_vars ee ⊆ FDOM env3` by(
        unabbrev_all_tac >> fs[] >>
        rw[env_to_Cenv_MAP,MAP_MAP_o] >>
        rw[combinTheory.o_DEF,pairTheory.LAMBDA_PROD,FST_pair] ) >>
      `∀v. v ∈ FRANGE env3 ⇒ Cclosed v` by(
        unabbrev_all_tac >>
        fs[env_to_Cenv_MAP] >>
        match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
        fs[MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD] >>
        rw[bind_def,MEM_MAP,pairTheory.EXISTS_PROD] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM,bind_def,MEM_MAP,pairTheory.EXISTS_PROD] >>
        PROVE_TAC[]) >>
      fs[] >> rw[] >>
      qmatch_assum_rename_tac `result_rel syneq r rr`[] >>
      `free_vars ee ⊆ FDOM env2` by (
        unabbrev_all_tac >> fs[] ) >>
      `∀v. v ∈ FRANGE env2 ⇒ Cclosed v` by (
        unabbrev_all_tac >> fs[] >>
        fs[extend_rec_env_def] >>
        qx_gen_tac `v` >>
        Cases_on `v=w2` >> fs[] >>
        match_mp_tac IN_FRANGE_DOMSUB_suff >>
        match_mp_tac IN_FRANGE_FUPDATE_suff >>
        fs[] >>
        rw[Once Cclosed_cases] ) >>
      qsuff_tac `∃x. Cevaluate (DRESTRICT env2 (free_vars ee)) ee x ∧ result_rel syneq rr x` >- (
        rw[] >>
        imp_res_tac Cevaluate_any_super_env >>
        metis_tac[result_rel_syneq_trans,result_rel_syneq_sym] ) >>
      qsuff_tac `fmap_rel syneq
                 (DRESTRICT env3 (free_vars ee))
                 (DRESTRICT env2 (free_vars ee))` >- (
        strip_tac >>
        qspecl_then [`DRESTRICT env2 (free_vars ee)`,
                     `DRESTRICT env3 (free_vars ee)`,
                     `ee`,`rr`] mp_tac Cevaluate_syneq_env >>
        fs[] >>
        fs[FDOM_DRESTRICT] >>
        PROVE_TAC[IN_FRANGE_DRESTRICT_suff] ) >>
      rw[fmap_rel_def,FDOM_DRESTRICT] >-
        fs[SUBSET_INTER_ABSORPTION,INTER_COMM] >>
      `x ∈ FDOM env2` by fs[SUBSET_DEF] >>
      rw[DRESTRICT_DEF] >>
      qunabbrev_tac `env3` >>
      qmatch_abbrev_tac `syneq (alist_to_fmap al ' x) (env2 ' x)` >>
      `∃v. ALOOKUP al x = SOME v` by (
        Cases_on `ALOOKUP al x` >> fs[] >>
        imp_res_tac ALOOKUP_FAILS >>
        unabbrev_all_tac >>
        fs[MEM_MAP,pairTheory.EXISTS_PROD] ) >>
      imp_res_tac ALOOKUP_SOME_FAPPLY_alist_to_fmap >>
      pop_assum(SUBST1_TAC) >>
      fs[Abbr`al`,env_to_Cenv_MAP,ALOOKUP_MAP] >>
      fs[bind_def] >- (
        rw[Abbr`env2`] >>
        rw[extend_rec_env_def] ) >>
      rw[Abbr`env2`,extend_rec_env_def] >>
      Cases_on`s=x`>>fs[FAPPLY_FUPDATE_THM] >- (
        fs[Abbr`ee`,NOT_fresh_var] >>
        fs[FLOOKUP_DEF,optionTheory.OPTREL_def] >>
        fsrw_tac[DNF_ss][] >>
        metis_tac[NOT_fresh_var,FINITE_FV,optionTheory.SOME_11]) >>
      fs[Abbr`ee`] >>
      PROVE_TAC[NOT_fresh_var,FINITE_FV]) >>
    fs[v_to_Cv_def,LET_THM,defs_to_Cdefs_MAP] >>
    fs[Q.SPEC`CRecClos env1 ns' defs X`syneq_cases] >>
    rw[] >> fs[] >> rw[] >>
    qpat_assum `X < LENGTH Y` assume_tac >>
    fs[EL_MAP] >>
    qmatch_assum_rename_tac `ALL_DISTINCT (MAP FST ns)`[] >>
    qabbrev_tac`q = EL n' ns` >>
    PairCases_on `q` >>
    pop_assum (mp_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def]) >> rw[] >>
    fs[] >> rw[] >>
    Cases_on `ALOOKUP ns q0` >> fs[] >>
    qmatch_assum_rename_tac `ALOOKUP ns q0 = SOME p`[] >>
    PairCases_on `p` >> fs[] >> rw[] >>
    `ALOOKUP ns q0 = SOME (q1,q2)` by (
      match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
      rw[MEM_EL] >> PROVE_TAC[] ) >>
    fs[] >> rw[] >>
    qmatch_assum_abbrev_tac`Cevaluate env3 ee r` >>
    Q.PAT_ABBREV_TAC`env2 = X:string|->Cv` >>
    qmatch_assum_abbrev_tac `result_rel syneq rr r` >>
    fs[Q.SPEC`Recclosure l ns q0`closed_cases] >>
    `free_vars ee ⊆ FDOM env2` by (
      first_x_assum (qspecl_then [`n'`,`[p0]`,`ee`] mp_tac) >>
      unabbrev_all_tac >> fs[] >>
      rw[EL_MAP] ) >>
    `∀v. v ∈ FRANGE env2 ⇒ Cclosed v` by (
      unabbrev_all_tac >> fs[] >>
      fs[extend_rec_env_def] >>
      qx_gen_tac `v` >>
      Cases_on `v=w2` >> fs[] >>
      match_mp_tac IN_FRANGE_DOMSUB_suff >>
      fs[FOLDL_FUPDATE_LIST] >>
      match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >> fs[] >>
      fs[MAP_MAP_o,MEM_MAP,pairTheory.EXISTS_PROD] >>
      fsrw_tac[DNF_ss][] >>
      rw[Once Cclosed_cases,MEM_MAP,pairTheory.EXISTS_PROD]
        >- PROVE_TAC[] >>
      first_x_assum match_mp_tac >>
      PROVE_TAC[]) >>
    qsuff_tac `∃x. Cevaluate (DRESTRICT env2 (free_vars ee)) ee x ∧ result_rel syneq rr x` >- (
      rw[] >>
      imp_res_tac Cevaluate_any_super_env >>
      metis_tac[result_rel_syneq_trans,result_rel_syneq_sym] ) >>
    `free_vars ee ⊆ FDOM env3` by(
      unabbrev_all_tac >> fs[] >>
      rw[env_to_Cenv_MAP,MAP_MAP_o] >>
      rw[combinTheory.o_DEF,pairTheory.LAMBDA_PROD,FST_pair] ) >>
    `∀v. v ∈ FRANGE env3 ⇒ Cclosed v` by(
      unabbrev_all_tac >>
      fs[env_to_Cenv_MAP] >>
      match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      fs[MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD] >>
      rw[bind_def,MEM_MAP,pairTheory.EXISTS_PROD] >>
      match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
      fs[EVERY_MEM,bind_def,MEM_MAP,pairTheory.EXISTS_PROD] >>
      PROVE_TAC[]) >>
    qspecl_then [`env3`,`ee`,`r`] mp_tac Cevaluate_free_vars_env >>
    fs[] >> rw[] >>
    qunabbrev_tac`rr` >>
    qmatch_assum_rename_tac `result_rel syneq r rr`[] >>
    qsuff_tac `fmap_rel syneq
               (DRESTRICT env3 (free_vars ee))
               (DRESTRICT env2 (free_vars ee))` >- (
      strip_tac >>
      qspecl_then [`DRESTRICT env2 (free_vars ee)`,
                   `DRESTRICT env3 (free_vars ee)`,
                   `ee`,`rr`] mp_tac Cevaluate_syneq_env >>
      fs[] >>
      fs[FDOM_DRESTRICT] >>
      PROVE_TAC[IN_FRANGE_DRESTRICT_suff,
                result_rel_syneq_trans] ) >>
    rw[fmap_rel_def,FDOM_DRESTRICT] >-
      fs[SUBSET_INTER_ABSORPTION,INTER_COMM] >>
    `x ∈ FDOM env2` by fs[SUBSET_DEF] >>
    rw[DRESTRICT_DEF] >>
    qunabbrev_tac `env3` >>
    qmatch_abbrev_tac `syneq (alist_to_fmap al ' x) (env2 ' x)` >>
    `∃v. ALOOKUP al x = SOME v` by (
      Cases_on `ALOOKUP al x` >> fs[] >>
      imp_res_tac ALOOKUP_FAILS >>
      unabbrev_all_tac >>
      fs[MEM_MAP,pairTheory.EXISTS_PROD] ) >>
    imp_res_tac ALOOKUP_SOME_FAPPLY_alist_to_fmap >>
    qpat_assum `alist_to_fmap al ' x = X`(SUBST1_TAC) >>
    qpat_assum `Cevaluate X ee rr` kall_tac >>
    fs[Abbr`al`,env_to_Cenv_MAP,ALOOKUP_MAP] >> rw[] >>
    fs[bind_def] >- (
      rw[Abbr`env2`] >>
      rw[extend_rec_env_def] ) >>
    Cases_on `p0=x`>>fs[] >- (
      rw[] >>
      rw[Abbr`env2`,extend_rec_env_def] ) >>
    qpat_assum `ALOOKUP X Y = SOME Z` mp_tac >>
    asm_simp_tac(srw_ss())[build_rec_env_def,bind_def,FOLDR_CONS_triple] >>
    rw[ALOOKUP_APPEND] >>
    Cases_on `MEM x (MAP FST ns)` >>
    fs[MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD,FST_pair] >- (
      qpat_assum `X = SOME v'` mp_tac >>
      qho_match_abbrev_tac `((case ALOOKUP (MAP ff ns) x of
        NONE => ALOOKUP l x | SOME v => SOME v) = SOME v') ⇒ P` >>
      `MAP FST (MAP ff ns) = MAP FST ns` by (
        asm_simp_tac(srw_ss())[LIST_EQ_REWRITE,Abbr`ff`] >>
        qx_gen_tac `y` >> strip_tac >>
        fs[MAP_MAP_o,combinTheory.o_DEF,EL_MAP] >>
        qabbrev_tac `yy = EL y ns` >>
        PairCases_on `yy` >> fs[] ) >>
      `ALL_DISTINCT (MAP FST (MAP ff ns))` by PROVE_TAC[] >>
      `MEM (x,Recclosure l ns x) (MAP ff ns)` by (
        rw[Abbr`ff`,MEM_MAP,pairTheory.EXISTS_PROD] >>
        fs[MEM_MAP,pairTheory.EXISTS_PROD] >>
        PROVE_TAC[] ) >>
      imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
      fs[] >> rw[Abbr`P`] >>
      rw[v_to_Cv_def] >>
      rw[Abbr`env2`,extend_rec_env_def,FOLDL_FUPDATE_LIST] >>
      rw[FAPPLY_FUPDATE_THM] >>
      ho_match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
      fs[MAP_MAP_o,combinTheory.o_DEF] >>
      fsrw_tac[ETA_ss][] >>
      fs[pairTheory.LAMBDA_PROD] >>
      fsrw_tac[DNF_ss][MEM_MAP,pairTheory.EXISTS_PROD] >>
      rw[Once syneq_cases] >>
      fs[defs_to_Cdefs_MAP] >>
      qmatch_assum_rename_tac `MEM (x,z0,z1) ns`[] >>
      map_every qexists_tac [`z0`,`z1`] >> fs[] >>
      rw[] >>
      fs[EVERY_MEM,pairTheory.FORALL_PROD] >>
      fs[MEM_MAP,pairTheory.EXISTS_PROD] >>
      fsrw_tac[DNF_ss][] >>
      fs[Abbr`Cenv`] >>
      fs[env_to_Cenv_MAP,ALOOKUP_MAP] >>
      fsrw_tac[ETA_ss][] >>
      rw[] >>
      first_x_assum (match_mp_tac o MP_CANON) >>
      PROVE_TAC[]) >>
    qpat_assum `X = SOME v'` mp_tac >>
    qho_match_abbrev_tac `((case ALOOKUP (MAP ff ns) x of
      NONE => ALOOKUP l x | SOME v => SOME v) = SOME v') ⇒ P` >>
    `MAP FST (MAP ff ns) = MAP FST ns` by (
      asm_simp_tac(srw_ss())[LIST_EQ_REWRITE,Abbr`ff`] >>
      qx_gen_tac `y` >> strip_tac >>
      fs[MAP_MAP_o,combinTheory.o_DEF,EL_MAP] >>
      qabbrev_tac `yy = EL y ns` >>
      PairCases_on `yy` >> fs[] ) >>
    `ALOOKUP (MAP ff ns) x= NONE` by (
      rw[ALOOKUP_NONE]) >>
    rw[Abbr`P`] >>
    rw[Abbr`env2`] >>
    rw[extend_rec_env_def,FOLDL_FUPDATE_LIST] >>
    rw[FAPPLY_FUPDATE_THM] >>
    ho_match_mp_tac FUPDATE_LIST_APPLY_HO_THM >>
    disj2_tac >>
    fs[MAP_MAP_o,combinTheory.o_DEF] >>
    fsrw_tac[ETA_ss][] >>
    fsrw_tac[DNF_ss][EVERY_MEM,pairTheory.FORALL_PROD] >>
    fsrw_tac[DNF_ss][optionTheory.OPTREL_def,FLOOKUP_DEF] >>
    fsrw_tac[DNF_ss][MEM_MAP,pairTheory.EXISTS_PROD] >>
    fs[Abbr`ee`] >>
    imp_res_tac ALOOKUP_MEM >>
    metis_tac[NOT_fresh_var,FINITE_FV,optionTheory.SOME_11])) >>
strip_tac >- rw[] >>
strip_tac >- (
  ntac 2 gen_tac >>
  Cases >> fs[exp_to_Cexp_def] >>
  qx_gen_tac `e1` >>
  qx_gen_tac `e2` >>
  rw[LET_THM] >- (
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj2_tac >>
    rw[Cevaluate_list_with_Cevaluate] >>
    rw[Cevaluate_list_with_cons] >>
    rpt (first_x_assum (qspec_then `m` mp_tac)) >>
    rw[] >>
    qmatch_assum_rename_tac `syneq (v_to_Cv m v1) w1`[] >>
    disj1_tac >>
    qexists_tac `w1` >> fs[] )
  >- (
    fs[] >>
    rpt (first_x_assum (qspec_then `m` mp_tac)) >>
    rw[] >>
    qmatch_assum_rename_tac `syneq (v_to_Cv m v1) w1`[] >>
    qmatch_assum_abbrev_tac `Cevaluate env0 exp0 (Rval w1)` >>
    `∀v. v ∈ FRANGE env0 ⇒ Cclosed v` by (
      imp_res_tac v_to_Cv_closed >>
      fs[FEVERY_DEF] >> PROVE_TAC[] ) >>
    `free_vars exp0 ⊆ FDOM env0` by (
      fs[Abbr`exp0`,Abbr`env0`,env_to_Cenv_MAP,MAP_MAP_o,
         pairTheory.LAMBDA_PROD,combinTheory.o_DEF,FST_pair] ) >>
    `every_result Cclosed (Rval w1)` by (
      match_mp_tac (MP_CANON Cevaluate_closed) >>
      map_every qexists_tac [`env0`,`exp_to_Cexp m e1`] >>
      fs[Abbr`env0`,env_to_Cenv_MAP,MAP_MAP_o,
         pairTheory.LAMBDA_PROD,combinTheory.o_DEF,FST_pair] ) >>
    fs[] >>
    BasicProvers.EVERY_CASE_TAC >>
    rw[Once Cevaluate_cases]
    >- (
      disj2_tac >>
      rw[Cevaluate_list_with_Cevaluate] >>
      rw[Cevaluate_list_with_cons] >>
      disj1_tac >>
      qexists_tac `w1` >> fs[] )
    >- (
      disj1_tac >>
      qexists_tac `w1` >> fs[] >>
      rw[Once Cevaluate_cases] >>
      disj2_tac >>
      match_mp_tac Cevaluate_FUPDATE_Rerr >>
      fs[env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,
         pairTheory.LAMBDA_PROD,FST_pair,
         fresh_var_not_in,FINITE_has_fresh_string] >>
      fs[Abbr`exp0`] >>
      fs[Abbr`env0`,env_to_Cenv_MAP,MAP_MAP_o,
         pairTheory.LAMBDA_PROD,combinTheory.o_DEF,FST_pair] )
    >- (
      disj2_tac >>
      rw[Cevaluate_list_with_Cevaluate] >>
      rw[Cevaluate_list_with_cons] >>
      rw[Once Cevaluate_cases] >>
      disj2_tac >>
      rw[Cevaluate_list_with_Cevaluate] >>
      rw[Cevaluate_list_with_cons] >>
      disj1_tac >>
      PROVE_TAC[] )
    >- (
      disj1_tac >>
      qexists_tac `w1` >>
      fs[] >>
      rw[Once Cevaluate_cases] >>
      disj2_tac >>
      match_mp_tac Cevaluate_FUPDATE_Rerr >>
      fs[fresh_var_not_in,FINITE_has_fresh_string] >>
      fs[Abbr`env0`,env_to_Cenv_MAP,MAP_MAP_o,
         pairTheory.LAMBDA_PROD,combinTheory.o_DEF,FST_pair] ))
  >- (
    rw[Once Cevaluate_cases] >>
    disj2_tac >>
    rw[Cevaluate_list_with_Cevaluate] >>
    rw[Cevaluate_list_with_cons] >>
    disj1_tac >>
    fsrw_tac[DNF_ss][] >>
    PROVE_TAC[] )
  >- (
    rw[Once Cevaluate_cases] >>
    disj2_tac >> disj1_tac >>
    fsrw_tac[DNF_ss][] >>
    rw[Cevaluate_list_with_Cevaluate] >>
    rw[Cevaluate_list_with_cons] >>
    PROVE_TAC[])) >>
strip_tac >- (
  ntac 2 gen_tac >>
  Cases >> fs[exp_to_Cexp_def] >>
  qx_gen_tac `e1` >>
  qx_gen_tac `e2` >>
  rw[LET_THM] >- (
    rw[Once Cevaluate_cases] >>
    rw[Cevaluate_list_with_Cevaluate] >>
    rw[Cevaluate_list_with_cons] )
  >- (
    BasicProvers.EVERY_CASE_TAC >>
    rw[Once Cevaluate_cases] >>
    rw[Cevaluate_list_with_Cevaluate] >>
    rw[Cevaluate_list_with_cons] >>
    disj2_tac >>
    rw[Once Cevaluate_cases] >>
    rw[Cevaluate_list_with_Cevaluate] >>
    rw[Cevaluate_list_with_cons])
  >- (
    rw[Once Cevaluate_cases] >>
    rw[Cevaluate_list_with_Cevaluate] >>
    rw[Cevaluate_list_with_cons] )
  >- (
    rw[Once Cevaluate_cases] )) >>
strip_tac >- (
  rw[exp_to_Cexp_def,LET_THM] >>
  fsrw_tac[DNF_ss][] >>
  imp_res_tac do_log_FV >>
  `FV exp' ⊆ set (MAP FST env)` by PROVE_TAC[SUBSET_TRANS] >>
  fsrw_tac[DNF_ss][] >>
  rpt (first_x_assum (qspec_then`m` mp_tac)) >>
  rw[] >>
  Cases_on `op` >> Cases_on `v` >> fs[do_log_def] >>
  Cases_on `l` >> fs[v_to_Cv_def] >>
  fs[Q.SPEC`CLitv l`syneq_cases] >> rw[] >>
  rw[Once Cevaluate_cases] >>
  fsrw_tac[DNF_ss][] >> disj1_tac >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `b` >> fs[] >>
  rw[] >> fs[] >> rw[] >>
  fs[evaluate_lit] >> rw[v_to_Cv_def] >>
  PROVE_TAC[result_rel_refl,syneq_refl] ) >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[exp_to_Cexp_def,LET_THM] >>
  Cases_on `op` >> fsrw_tac[DNF_ss][] >>
  rw[Once Cevaluate_cases] ) >>
strip_tac >- (
  rw[exp_to_Cexp_def,LET_THM] >>
  fsrw_tac[DNF_ss][] >>
  imp_res_tac do_if_FV >>
  `FV exp' ⊆ set (MAP FST env)` by (
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    PROVE_TAC[]) >> fs[] >>
  rw[Once Cevaluate_cases] >>
  fsrw_tac[DNF_ss][] >>
  disj1_tac >>
  qpat_assum `do_if v e2 e3 = X` mp_tac >>
  fs[do_if_def] >> rw[] >|[
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`T`,
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`F`] >>
  fsrw_tac[DNF_ss][v_to_Cv_def,Q.SPEC`CLitv l`syneq_cases] ) >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[exp_to_Cexp_def,LET_THM] >>
  rw[Once Cevaluate_cases] ) >>
strip_tac >- (
  rpt strip_tac >> fs[] >>
  first_x_assum (qspec_then `m` mp_tac) >> rw[] >>
  qmatch_assum_rename_tac `syneq (v_to_Cv m v) w`[] >>
  rw[exp_to_Cexp_def,LET_THM] >>
  rw[Once Cevaluate_cases] >>
  srw_tac[DNF_ss][] >>
  disj1_tac >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `w` >> fs[] >>
  qmatch_assum_abbrev_tac `evaluate_match_with P cenv env v pes res` >>
  Q.ISPECL_THEN [`pes`,`res`] mp_tac evaluate_match_with_matchres >> fs[] >>
  strip_tac >>
  qmatch_assum_abbrev_tac `evaluate_match_with (matchres env) cenv env v pes r` >>
  Q.ISPECL_THEN [`pes`,`r`] mp_tac evaluate_match_with_Cevaluate_match >>
  fs[Abbr`r`] >>
  disch_then (qspec_then `m` mp_tac) >>
  rw[] >- (
    qmatch_assum_abbrev_tac `Cevaluate_match vv ppes FEMPTY NONE` >>
    `Cevaluate_match vv (MAP (λ(p,e). (p, exp_to_Cexp m e)) ppes) FEMPTY NONE` by (
      metis_tac [Cevaluate_match_MAP_exp, optionTheory.OPTION_MAP_DEF] ) >>
    qmatch_assum_abbrev_tac `Cevaluate_match vv (MAP ff ppes) FEMPTY NONE` >>
    `MAP ff ppes = pes_to_Cpes m pes` by (
      unabbrev_all_tac >>
      rw[pes_to_Cpes_MAP,LET_THM] >>
      rw[MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD] >>
      rw[pairTheory.UNCURRY] ) >>
    fs[] >>
    unabbrev_all_tac >>
    pop_assum kall_tac >>
    pop_assum mp_tac >>
    pop_assum kall_tac >>
    strip_tac >>
    cheat (* Cevaluate_match_remove_mat_var *) ) >>
  qmatch_assum_abbrev_tac `Cevaluate_match vv ppes eenv (SOME mr)` >>
  `Cevaluate_match vv (MAP (λ(p,e). (p, exp_to_Cexp m e)) ppes) eenv (SOME (exp_to_Cexp m mr))` by (
    metis_tac [Cevaluate_match_MAP_exp, optionTheory.OPTION_MAP_DEF] ) >>
  pop_assum mp_tac >>
  unabbrev_all_tac >>
  pop_assum kall_tac >>
  strip_tac >>
  qmatch_assum_abbrev_tac `Cevaluate_match vv (MAP ff ppes) eenv mmr` >>
  `MAP ff ppes = pes_to_Cpes m pes` by (
    unabbrev_all_tac >>
    rw[pes_to_Cpes_MAP,LET_THM] >>
    rw[MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD] >>
    rw[pairTheory.UNCURRY] ) >>
  fs[] >>
  unabbrev_all_tac >>
  pop_assum kall_tac >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  fs[] >>
  `every_result closed (Rval v)` by (
    match_mp_tac (MP_CANON evaluate_closed) >>
    PROVE_TAC[] ) >>
  Q.ISPECL_THEN [`pes`,`Rval (menv,mr)`] mp_tac evaluate_match_with_matchres_closed >>
  fs[] >> strip_tac >>
  `FV mr ⊆ set (MAP FST menv) ∪ set (MAP FST env)` by (
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    fsrw_tac[DNF_ss][pairTheory.FORALL_PROD,MEM_MAP,pairTheory.EXISTS_PROD] >>
    fsrw_tac[DNF_ss][EXTENSION,MEM_MAP,pairTheory.EXISTS_PROD] >>
    PROVE_TAC[] ) >>
  fs[] >>
  disch_then (qspec_then `m` mp_tac) >>
  rw[] >>
  cheat (* Cevaluate_match_remove_mat_var *) ) >>
cheat)

val Cpat_nice_ind =
TypeBase.induction_of(``:Cpat``)
|> Q.SPECL[`P`,`EVERY P`]
|> SIMP_RULE(srw_ss())[]
|> UNDISCH_ALL
|> CONJUNCT1
|> DISCH_ALL
|> Q.GEN`P`

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
