open HolKernel bossLib boolLib Parse termTheory chap2Theory chap3Theory reductionEval binderLib relationTheory lcsymtacs

val _ = new_theory "abselim"

val _ = remove_ovl_mapping "LAM" {Name="LAM", Thy="labelledTerms"}
val _ = clear_overloads_on "FV"
val _ = overload_on ("FV", ``supp tpm``)
val _ = remove_ovl_mapping "VAR" {Name="VAR", Thy="labelledTerms"}
val _ = remove_ovl_mapping "APP"  {Name="APP", Thy="labelledTerms"}

val (absfree_rules,absfree_ind,absfree_cases) = Hol_reln`
  (absfree S) ∧ (absfree K) ∧ (absfree (VAR x)) ∧
  (absfree t1 ∧ absfree t2 ⇒ absfree (APP t1 t2))`

val (abselim_rules,abselim_ind,abselim_cases) = Hol_reln`
  (abselim (VAR x) (VAR x)) ∧
  (abselim t1 t1' ∧ abselim t2 t2' ⇒ abselim (t1 @@ t2) (t1' @@ t2')) ∧
  (abselim t t' ∧ x ∉ FV t ⇒ abselim (LAM x t) (K @@ t')) ∧
  (abselim (LAM x (VAR x)) (S @@ K @@ K)) ∧
  (abselim (LAM y t) r1 ∧ abselim (LAM x r1) r2
   ∧ x ∈ FV (LAM y t) ∧ (LAM x (LAM y t) ≠ S) ∧ (LAM x (LAM y t) ≠ K)
    ⇒ abselim (LAM x (LAM y t)) r2) ∧
  (abselim (LAM x t1) t1' ∧ abselim (LAM x t2) t2' ∧ x ∈ FV (t1 @@ t2)
    ⇒ abselim (LAM x (t1 @@ t2)) (S @@ t1' @@ t2')) ∧
  (abselim S S) ∧ (abselim K K)`

val abselim_absfree = store_thm(
"abselim_absfree",
``∀t u. abselim t u ⇒ absfree u``,
ho_match_mp_tac abselim_ind >>
srw_tac [][absfree_rules])

val absfree_abselim_id = store_thm(
"absfree_abselim_id",
``∀t. absfree t ⇒ abselim t t``,
ho_match_mp_tac absfree_ind >>
srw_tac [][abselim_rules]);

val lameq_lamext = store_thm(
"lameq_lamext",
``∀t u. t == u ⇒ lamext t u``,
ho_match_mp_tac lameq_ind >>
metis_tac [lamext_rules])

val lamext_refl = store_thm(
  "lamext_refl",
  ``lamext M M``,
  SRW_TAC [][lamext_rules]);
val _ = export_rewrites["lamext_refl"];

val lamext_app_cong = store_thm(
  "lamext_app_cong",
  ``lamext M1 M2 ==> lamext N1 N2 ==> lamext (M1 @@ N1) (M2 @@ N2)``,
  METIS_TAC [lamext_rules]);

val [_,lamext_refl,lamext_sym,lamext_trans,_,_,_,lamext_ext] = CONJUNCTS lamext_rules
val [_,conversion_sym,conversion_trans,conversion_subset,_,_] = CONJUNCTS (SPEC_ALL conversion_rules)

val lamext_betaeta = store_thm(
"lamext_betaeta",
``lamext = conversion (β RUNION η)``,
metis_tac [lemma2_14,beta_eta_lameta,FUN_EQ_THM]);

val abselim_lamext = store_thm(
"abselim_lamext",
``∀t u. abselim t u ⇒ lamext t u``,
ho_match_mp_tac abselim_ind >>
conj_tac >- srw_tac [][] >>
conj_tac >- srw_tac [][lamext_app_cong] >>
conj_tac >- (
  map_every qx_gen_tac [`t`,`u`,`x`] >>
  strip_tac >>
  match_mp_tac lamext_ext >>
  Q_TAC (NEW_TAC "z") `FV (LAM x t @@ (K @@ u))` >>
  qexists_tac `z` >> conj_tac >- fsrw_tac [][] >>
  srw_tac [][lamext_betaeta] >>
  match_mp_tac conversion_trans >>
  qexists_tac `t` >>
  conj_tac >- (
    match_mp_tac conversion_subset >>
    srw_tac [][RUNION,beta_def] >>
    disj1_tac >>
    map_every qexists_tac [`x`,`t`] >>
    srw_tac [][lemma14b] ) >>
  match_mp_tac conversion_trans >>
  qexists_tac `u` >>
  conj_tac >- (
    srw_tac [][SYM lamext_betaeta] ) >>
  srw_tac [][SYM lamext_betaeta] >>
  match_mp_tac lameq_lamext >>
  srw_tac [BETA_ss][] ) >>
conj_tac >- (
  srw_tac [][] >>
  match_mp_tac lamext_ext >>
  Q_TAC (NEW_TAC "z") `FV (LAM x (VAR x) @@ (S @@ K @@ K))` >>
  qexists_tac `z` >> srw_tac [][] >>
  match_mp_tac lameq_lamext >>
  srw_tac [BETA_ss][] ) >>
conj_tac >-
  metis_tac [lamext_rules] >>
conj_tac >- (
  rpt gen_tac >>
  strip_tac >>
  pop_assum (K ALL_TAC) >>
  match_mp_tac lamext_ext >>
  Q_TAC (NEW_TAC "z") `FV (LAM x (t1 @@ t2) @@ (S @@ t1' @@ t2'))` >>
  qexists_tac `z` >> fsrw_tac [][] >>
  match_mp_tac lamext_sym >>
  match_mp_tac lamext_trans >>
  qexists_tac `S @@ (LAM x t1) @@ (LAM x t2) @@ VAR z` >>
  conj_tac >- PROVE_TAC [lamext_rules] >>
  match_mp_tac lameq_lamext >>
  srw_tac [BETA_ss][] ) >>
srw_tac [][lamext_refl]);

val lemma1 = prove(
``x ∉ FV t ⇒ (LAM x (tpm [(x,y)] t) = LAM y t)``,
srw_tac [][LAM_eq_thm] >>
Cases_on `x=y` >> srw_tac [][])

val lemma2 = prove(
``(LAM (swapstr x y v) (tpm [(x,y)] t) = S) = (LAM v t = S)``,
srw_tac [][EQ_IMP_THM] >- (
  `tpm [(x,y)] (LAM (swapstr x y v) (tpm [(x,y)] t)) = tpm [(x,y)] S` by
    metis_tac [] >>
  fsrw_tac [][] >> srw_tac [][tpm_fresh] ) >>
`tpm [(x,y)] (LAM v t) = tpm [(x,y)] S` by metis_tac [] >>
fsrw_tac [][] >> srw_tac [][tpm_fresh])

val lemma3 = prove(
``(LAM (swapstr x y v) (tpm [(x,y)] t) = K) = (LAM v t = K)``,
srw_tac [][EQ_IMP_THM] >- (
  `tpm [(x,y)] (LAM (swapstr x y v) (tpm [(x,y)] t)) = tpm [(x,y)] K` by
    metis_tac [] >>
  fsrw_tac [][] >> srw_tac [][tpm_fresh] ) >>
`tpm [(x,y)] (LAM v t) = tpm [(x,y)] K` by metis_tac [] >>
fsrw_tac [][] >> srw_tac [][tpm_fresh])

val lam_count_exists =
  tm_recursion
|> INST_TYPE [alpha |-> ``:num``]
|> Q.INST [`apm`|->`K I`,`A`|->`{}`,
           `vr`|->`K 0`,
           `ap`|->`λm n t1 t2. m + n`,
           `lm`|->`λm v t. if (LAM v t = S) ∨ (LAM v t = K) then 0 else m + 1`]
|> SIMP_RULE (srw_ss()) [lemma1,lemma2,lemma3]

val lam_count_def = new_specification ("lam_count_def",["lam_count"],lam_count_exists)

val app_count_exists =
  tm_recursion
|> INST_TYPE [alpha |-> ``:num``]
|> Q.INST [`apm`|->`K I`,`A`|->`{}`,
           `vr`|->`K 0`,
           `ap`|->`λm n t1 t2. m + n + 1`,
           `lm`|->`λm v t. if (LAM v t = S) ∨ (LAM v t = K) then 0 else m`]
|> SIMP_RULE (srw_ss()) [lemma1,lemma2,lemma3]

val app_count_def = new_specification ("app_count_def",["app_count"],app_count_exists)

val _ = export_rewrites["lam_count_def","app_count_def"];

val lam_count_absfree = store_thm(
"lam_count_absfree",
``∀t. absfree t ⇒ (lam_count t = 0)``,
ho_match_mp_tac absfree_ind >>
srw_tac [][S_def,K_def])

val abselim_total = store_thm(
"abselim_total",
``∀t.∃u. abselim t u``,
WF_INDUCTION_THM
 |> Q.ISPEC `inv_image ($< LEX $<) (λt. (lam_count t, app_count t))`
 |> SIMP_RULE (srw_ss()) [pairTheory.WF_LEX,prim_recTheory.WF_LESS,relationTheory.WF_inv_image]
 |> ho_match_mp_tac >>
srw_tac [][relationTheory.inv_image_def,prim_recTheory.measure_def,pairTheory.LEX_DEF] >>
FULL_STRUCT_CASES_TAC (Q.SPEC `t` term_CASES) >- (
  fsrw_tac [][] >> metis_tac [abselim_rules] )
>- (
  `(∃u. abselim t1 u) ∧ (∃u. abselim t2 u)` by (
    srw_tac [][] >> first_x_assum match_mp_tac >>
    srw_tac [ARITH_ss][] ) >>
  metis_tac [abselim_rules] ) >>
qmatch_rename_tac `∃u. abselim (LAM x t) u` [] >>
Cases_on `LAM x t = S` >- metis_tac [abselim_rules] >>
Cases_on `LAM x t = K` >- metis_tac [abselim_rules] >>
Cases_on `x ∉ FV t` >- (
  `∃u. abselim t u` by (
    first_x_assum match_mp_tac >>
    srw_tac [ARITH_ss][] ) >>
  metis_tac [abselim_rules] ) >> fsrw_tac [][] >>
FULL_STRUCT_CASES_TAC (Q.SPEC `t` term_CASES) >- (
  fsrw_tac [][] >> metis_tac [abselim_rules] )
>- (
  `(∃u. abselim (LAM x t1) u) ∧ (∃u. abselim (LAM x t2) u)` by (
    srw_tac [][] >> first_x_assum match_mp_tac >>
    srw_tac [ARITH_ss][] ) >>
  `x ∈ FV t1 ∪ FV t2` by fsrw_tac [][] >>
  metis_tac [abselim_rules] ) >>
qmatch_rename_tac `∃u. abselim (LAM x (LAM y t)) u` [] >>
`∃r1. abselim (LAM y t) r1` by (
  first_x_assum match_mp_tac >>
  srw_tac [ARITH_ss][] ) >>
`x ∈ FV t` by fsrw_tac [][] >>
qsuff_tac `∃r2. abselim (LAM x r1) r2` >- metis_tac [abselim_rules] >>
first_x_assum match_mp_tac >>
disj1_tac >>
Cases_on `LAM x r1 = S` >- srw_tac [ARITH_ss][] >>
Cases_on `LAM x r1 = K` >- srw_tac [ARITH_ss][] >>
`absfree r1` by metis_tac [abselim_absfree] >>
`lam_count r1 = 0` by metis_tac [lam_count_absfree] >>
Cases_on `LAM y t = S` >- (
  `x ∈ FV S` by metis_tac [] >> fsrw_tac [][S_def] ) >>
Cases_on `LAM y t = K` >- (
  `x ∈ FV K` by metis_tac [] >> fsrw_tac [][K_def] ) >>
srw_tac [ARITH_ss][])

val [abselim_VAR,abselim_APP,abselim_LAM,abselim_LAM_VAR,abselim_LAM_LAM,abselim_LAM_APP,abselim_S,abselim_K] = CONJUNCTS abselim_rules

val abselim_tpm = store_thm(
"abselim_tpm",
``∀t u. abselim t u ⇒ ∀x y. abselim (tpm [(x,y)] t) (tpm [(x,y)] u)``,
ho_match_mp_tac abselim_ind >>
conj_tac >- srw_tac [][abselim_VAR] >>
conj_tac >- srw_tac [][abselim_APP] >>
conj_tac >- srw_tac [][abselim_LAM,tpm_fresh] >>
conj_tac >- srw_tac [][abselim_LAM_VAR,tpm_fresh] >>
conj_tac >- (
  srw_tac [][] >>
  match_mp_tac abselim_LAM_LAM >>
  srw_tac [][] >>
  qexists_tac `(tpm [(x',y')] u)` >>
  `tpm [(x',y')] (LAM x (LAM y t)) ≠ tpm [(x',y')] S` by metis_tac [tpm_inverse] >>
  `tpm [(x',y')] (LAM x (LAM y t)) ≠ tpm [(x',y')] K` by metis_tac [tpm_inverse] >>
  fsrw_tac [][tpm_fresh] ) >>
conj_tac >- (
  rpt gen_tac >>
  strip_tac >>
  rpt gen_tac >>
  asm_simp_tac (srw_ss()) [tpm_fresh] >>
  match_mp_tac abselim_LAM_APP >>
  fsrw_tac [][] ) >>
srw_tac [][tpm_fresh,abselim_S,abselim_K]);

val abselim_FV = store_thm(
"abselim_FV",
``∀t u. abselim t u ⇒ (FV t = FV u)``,
ho_match_mp_tac abselim_ind >>
conj_tac >- srw_tac [][] >>
conj_tac >- srw_tac [][] >>
conj_tac >- fsrw_tac [][pred_setTheory.DELETE_NON_ELEMENT] >>
conj_tac >- srw_tac [][] >>
conj_tac >- srw_tac [][] >>
conj_tac >- fsrw_tac [][pred_setTheory.DELETE_NON_ELEMENT,pred_setTheory.UNION_DELETE] >>
srw_tac [][]);

val abselim_unique = store_thm(
"abselim_unique",
``∀t u1 u2. abselim t u1 ∧ abselim t u2 ⇒ (u1 = u2)``,
qsuff_tac `∀t u1. abselim t u1 ⇒ ∀u2. abselim t u2 ⇒ (u1 = u2)` >- metis_tac [] >>
ho_match_mp_tac abselim_ind >>
conj_tac >- (
  srw_tac [][] >>
  qspecl_then [`VAR x`,`u2`] mp_tac abselim_cases >>
  fsrw_tac [][] >>
  srw_tac [][S_def,K_def] ) >>
conj_tac >- (
  map_every qx_gen_tac [`t1`,`v1`,`t2`,`v2`] >>
  srw_tac [][] >>
  qspecl_then [`t1@@t2`,`u2`] mp_tac abselim_cases >>
  fsrw_tac [][S_def,K_def] >>
  srw_tac [][] >> srw_tac [][] ) >>
conj_tac >- (
  srw_tac [][] >>
  qspecl_then [`LAM x t`,`u2`] mp_tac abselim_cases >>
  fsrw_tac [][] >>
  srw_tac [][] >-
    fsrw_tac [][LAM_eq_thm,tpm_fresh]
  >- (
    fsrw_tac [][LAM_eq_thm] >>
    fsrw_tac [][] )
  >- (
    fsrw_tac [][LAM_eq_thm] >> srw_tac [][] >>
    fsrw_tac [][] >>
    Cases_on `x=y` >> fsrw_tac [][] )
  >- (
    fsrw_tac [][LAM_eq_thm] >> srw_tac [][] >>
    fsrw_tac [][] )
  >- (
    fsrw_tac [][LAM_eq_thm] >> srw_tac [][] >>
    fsrw_tac [][] )
  >- (
    fsrw_tac [][LAM_eq_thm,S_def] >> srw_tac [][] >>
    fsrw_tac [][] >>
    Cases_on `x = "x"` >> fsrw_tac [][] >>
    Cases_on `x = "y"` >> fsrw_tac [][] >>
    Cases_on `x = "z"` >> fsrw_tac [][] ) >>
  fsrw_tac [][K_def,LAM_eq_thm] >> srw_tac [][] >>
  fsrw_tac [][] >>
  Cases_on `x = "x"` >> fsrw_tac [][] >>
  Cases_on `x = "y"` >> fsrw_tac [][] ) >>
conj_tac >- (
  srw_tac [][] >>
  qspecl_then [`LAM x (VAR x)`,`u2`] mp_tac abselim_cases >>
  fsrw_tac [][LAM_eq_thm] >>
  srw_tac [][] >> fsrw_tac [][] >>
  fsrw_tac [][tpm_eqr] >> srw_tac [][] >>
  fsrw_tac [][] >>
  fsrw_tac [][S_def,K_def,LAM_eq_thm] ) >>
conj_tac >- (
  srw_tac [][] >>
  qspecl_then [`LAM x (LAM y t)`,`u2`] mp_tac abselim_cases >>
  full_simp_tac std_ss [term_distinct] >>
  strip_tac >- (
    fsrw_tac [][LAM_eq_thm] >>
    srw_tac [][] >> fsrw_tac [][] >>
    fsrw_tac [][tpm_eqr] >>
    srw_tac [][] >>
    fsrw_tac [][] >>
    qpat_assum `x <> x'` assume_tac >>
    qpat_assum `x <> y` assume_tac >>
    Cases_on`x'=y` >> fsrw_tac [][] )
  >- ( fsrw_tac [][LAM_eq_thm] )
  >- (
    Cases_on `x=x'` >- (
      qpat_assum `LAM x tt = LAM x' ttt` mp_tac >>
      asm_simp_tac (srw_ss()) [Once LAM_eq_thm] >>
      metis_tac [] ) >>
    qpat_assum `LAM x tt = LAM x' ttt` mp_tac >>
    asm_simp_tac (srw_ss()) [Once LAM_eq_thm] >>
    `abselim (tpm [(x,x')] (LAM y' t')) (tpm [(x,x')] r1)` by metis_tac [abselim_tpm] >>
    fsrw_tac [][] >> rpt strip_tac >>
    fsrw_tac [][] >>
    `u1 = tpm [(x,x')] r1` by metis_tac [] >>
    fsrw_tac [][] >>
    `abselim (tpm [(x,x')] (LAM x' r1)) (tpm [(x,x')] u2)` by metis_tac [abselim_tpm] >>
    fsrw_tac [][] >>
    `u1' = tpm [(x,x')] u2` by metis_tac [] >>
    srw_tac [][] >>
    match_mp_tac tpm_fresh >>
    `FV u2 = FV (LAM x' r1)` by metis_tac [abselim_FV] >>
    fsrw_tac [][] >>
    `FV r1 = FV (LAM y' t')` by metis_tac [abselim_FV] >>
    fsrw_tac [][] >>
    Cases_on `x=y'` >> fsrw_tac [][] ) >>
  fsrw_tac [][LAM_eq_thm] ) >>
conj_tac >- (
  rpt gen_tac >>
  strip_tac >>
  gen_tac >> strip_tac >>
  qspecl_then [`LAM x (t1 @@ t2)`,`u2`] mp_tac abselim_cases >>
  qabbrev_tac `fva = (x ∈ FV (t1 @@ t2))` >>
  fsrw_tac [][] >>
  qpat_assum `abselim (LAM x (t1 @@ t2)) u2` (K ALL_TAC) >>
  fsrw_tac [][S_def,LAM_eq_thm,K_def] >>
  fsrw_tac [][GSYM S_def, GSYM K_def] >>
  qmatch_abbrev_tac `aa ∨ bb ⇒ cc` >>
  strip_tac >- (
    unabbrev_all_tac >>
    fsrw_tac [][tpm_eqr] >> srw_tac [][] >>
    fsrw_tac [][] ) >>
  qunabbrev_tac `aa` >>
  full_simp_tac std_ss [Abbr`cc`,Abbr`bb`,(GSYM pred_setTheory.IN_UNION)] >-
    fsrw_tac [][] >>
  qabbrev_tac `fva' = x' ∈ FV t1' ∪ FV t2'` >>
  qpat_assum `Abbrev (fva = X)` assume_tac >>
  fsrw_tac [][] >>
  `abselim (tpm [(x,x')] (LAM x' t1')) (tpm [(x,x')] t1'')` by metis_tac [abselim_tpm] >>
  `abselim (tpm [(x,x')] (LAM x' t2')) (tpm [(x,x')] t2'')` by metis_tac [abselim_tpm] >>
  fsrw_tac [][] >>
  res_tac >>
  `(FV t1'' = FV (LAM x' t1')) ∧ (FV t2'' = FV (LAM x' t2'))` by metis_tac [abselim_FV] >>
  srw_tac [][tpm_fresh] ) >>
conj_tac >- (
  srw_tac [][] >>
  qspecl_then [`S`,`u2`] mp_tac abselim_cases >>
  srw_tac [][]
  >- srw_tac [][S_def]
  >- fsrw_tac [][S_def]
  >- (
    fsrw_tac [][S_def,LAM_eq_thm] >- (
      srw_tac [][] >> fsrw_tac [][] ) >>
    fsrw_tac [][tpm_eqr] >> srw_tac [][] >>
    fsrw_tac [][] >>
    Cases_on `x="x"` >> fsrw_tac [][] >>
    Cases_on `x="y"` >> fsrw_tac [][] >>
    Cases_on `x="z"` >> fsrw_tac [][] )
  >- ( fsrw_tac [][S_def,LAM_eq_thm] )
  >- ( metis_tac [] )
  >- ( fsrw_tac [][S_def,LAM_eq_thm] )
  >- ( fsrw_tac [][S_def,LAM_eq_thm] )
  >- ( fsrw_tac [][] ) ) >>
srw_tac [][] >>
qspecl_then [`K`,`u2`] mp_tac abselim_cases >>
srw_tac [][]
>- srw_tac [][K_def]
>- fsrw_tac [][K_def]
>- (
  fsrw_tac [][K_def,LAM_eq_thm] >- (
    srw_tac [][] >> fsrw_tac [][] ) >>
  fsrw_tac [][tpm_eqr] >> srw_tac [][] >>
  fsrw_tac [][] >>
  Cases_on `x="x"` >> fsrw_tac [][] >>
  Cases_on `x="y"` >> fsrw_tac [][] )
>- ( fsrw_tac [][K_def,LAM_eq_thm] )
>- ( metis_tac [] )
>- ( fsrw_tac [][K_def,LAM_eq_thm] )
>- ( fsrw_tac [][K_def,LAM_eq_thm] )
>- ( fsrw_tac [][] ) )

val _ = export_theory ()
