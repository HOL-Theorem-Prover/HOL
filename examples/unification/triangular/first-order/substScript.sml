open HolKernel boolLib bossLib Parse pred_setTheory relationTheory
finite_mapTheory termTheory ramanaLib whileTheory
prim_recTheory arithmeticTheory bagTheory listTheory;

val _ = new_theory "subst";

val FUNPOW_extends_mono = Q.store_thm(
"FUNPOW_extends_mono",
`∀P f. (∀x. P x ⇒ P (f x)) ∧ P x ⇒ P (FUNPOW f n x)`,
STRIP_TAC THEN Induct_on `n` THEN SRW_TAC [][FUNPOW_SUC]);

val _ = type_abbrev ("subst", ``:(num |-> 'a term)``);

val rangevars_def = Define`
  rangevars s = BIGUNION (IMAGE vars (FRANGE s))`;

val FINITE_rangevars = RWstore_thm(
"FINITE_rangevars",
`FINITE (rangevars s)`,
SRW_TAC [][rangevars_def] THEN SRW_TAC [][]);

val IN_FRANGE_rangevars = Q.store_thm(
"IN_FRANGE_rangevars",
`t ∈ FRANGE s ⇒ vars t SUBSET rangevars s`,
SRW_TAC [][rangevars_def,SUBSET_DEF] THEN METIS_TAC []);

val rangevars_FUPDATE = Q.store_thm(
"rangevars_FUPDATE",
`v ∉ FDOM s ⇒ (rangevars (s |+ (v,t)) = rangevars s UNION vars t)`,
SRW_TAC [][rangevars_def,DOMSUB_NOT_IN_DOM,UNION_COMM]);

val substvars_def = Define`
  substvars s = FDOM s UNION rangevars s`;

val FINITE_substvars = RWstore_thm(
"FINITE_substvars",
`FINITE (substvars s)`,
SRW_TAC [][substvars_def]);

val vR_def = Define`
  vR s y x = case FLOOKUP s x of SOME t -> y IN vars t || _ -> F`;

val wfs_def = Define`wfs s = WF (vR s)`;

val wfs_FEMPTY = RWstore_thm(
"wfs_FEMPTY",
`wfs FEMPTY`,
SRW_TAC [][wfs_def] THEN
Q_TAC SUFF_TAC `vR FEMPTY = EMPTY_REL` THEN1 METIS_TAC [WF_EMPTY_REL] THEN
SRW_TAC [][FUN_EQ_THM,vR_def]);

val wfs_SUBMAP = Q.store_thm(
"wfs_SUBMAP",
`wfs sx /\ s SUBMAP sx ==> wfs s`,
SRW_TAC [][wfs_def,SUBMAP_DEF] THEN
Q_TAC SUFF_TAC `!y x.vR s y x ==> vR sx y x`
  THEN1 METIS_TAC [WF_SUBSET] THEN
SRW_TAC [][vR_def,FLOOKUP_DEF] THEN
METIS_TAC []);

val wfs_no_cycles = Q.store_thm(
  "wfs_no_cycles",
  `wfs s <=> !v. ~(vR s)^+ v v`,
  EQ_TAC THEN1 METIS_TAC [WF_TC,wfs_def,WF_NOT_REFL] THEN
  SRW_TAC [] [wfs_def,WF_IFF_WELLFOUNDED,wellfounded_def] THEN
  SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
  `!n. (f n) IN FDOM s /\ f (SUC n) IN vars (s ' (f n))` by
    (STRIP_TAC THEN Q.PAT_ASSUM `!n.vR s (f (SUC n)) (f n)` (Q.SPEC_THEN `n` MP_TAC)
     THEN FULL_SIMP_TAC (srw_ss()) [vR_def] THEN Cases_on `FLOOKUP s (f n)` THEN
     Q.PAT_ASSUM `FLOOKUP s (f n) = Z` MP_TAC THEN SRW_TAC [] [FLOOKUP_DEF])
  THEN
  `!n m. (vR s)^+ (f (SUC (n + m))) (f n)` by
    (REPEAT STRIP_TAC THEN Induct_on `m` THEN1
       (SRW_TAC [] [] THEN METIS_TAC [TC_SUBSET]) THEN
     Q.PAT_ASSUM `!n. f n IN FDOM s /\ Z` (Q.SPEC_THEN `SUC (n + m)` MP_TAC)
     THEN SRW_TAC [] [] THEN
     `(vR s) (f (SUC (SUC (n + m)))) (f (SUC (n + m)))` by METIS_TAC
     [vR_def,FLOOKUP_DEF] THEN METIS_TAC [TC_RULES,ADD_SUC])
  THEN
  `?n m. f (SUC (n + m)) = f n` by
    (`~INJ f (count (SUC (CARD (FDOM s)))) (FDOM s)`
         by (SRW_TAC [] [PHP,CARD_COUNT,COUNT_SUC,CARD_DEF]) THEN
     FULL_SIMP_TAC (srw_ss()) [INJ_DEF] THEN1 METIS_TAC [] THEN
     ASSUME_TAC (Q.SPECL [`x`,`y`] LESS_LESS_CASES) THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN1 METIS_TAC [] THENL [
       Q.EXISTS_TAC `x` THEN Q.EXISTS_TAC `y - x - 1`,
       Q.EXISTS_TAC `y` THEN Q.EXISTS_TAC `x - y - 1`
     ] THEN SRW_TAC [ARITH_ss] [ADD1])
  THEN METIS_TAC []);

val subst_APPLY_def = Define`
  (subst_APPLY s (Var v) = case FLOOKUP s v of NONE -> Var v || SOME t -> t) /\
  (subst_APPLY s (Pair t1 t2) = Pair (subst_APPLY s t1) (subst_APPLY s t2)) /\
  (subst_APPLY s (Const c) = Const c)`;
val _ = set_fixity "''" (Infixr 700);
val _ = overload_on ("''", ``subst_APPLY``);
val _ = export_rewrites["subst_APPLY_def"];

val subst_APPLY_FAPPLY = Q.store_thm(
"subst_APPLY_FAPPLY",
`v IN FDOM s ==> (s ' v = s '' (Var v))`,
SRW_TAC [][subst_APPLY_def,FLOOKUP_DEF]);

val noids_def = Define`
  noids s = ∀v. FLOOKUP s v ≠ SOME (Var v)`;

val subst_APPLY_id = Q.store_thm(
"subst_APPLY_id",
`(s '' t = t) <=> !v.v IN (vars t) ∧ v IN FDOM s ⇒ (s ' v = Var v)`,
EQ_TAC THEN
Induct_on `t` THEN SRW_TAC [][FLOOKUP_DEF] THEN
FULL_SIMP_TAC (srw_ss()) []);

val idempotent_def = Define`
  idempotent s = !t.s '' (s '' t) = s '' t`;

val wfs_noids = Q.store_thm(
"wfs_noids",
`wfs s ⇒ noids s`,
SRW_TAC [][wfs_no_cycles,noids_def] THEN
SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
FIRST_X_ASSUM (Q.SPEC_THEN `v` MP_TAC) THEN
SRW_TAC [][] THEN MATCH_MP_TAC TC_SUBSET THEN
SRW_TAC [][vR_def]);

val idempotent_rangevars = Q.store_thm(
"idempotent_rangevars",
`idempotent s ∧ noids s <=> DISJOINT (FDOM s) (rangevars s)`,
EQ_TAC THEN1 (
  SRW_TAC [][DISJOINT_BIGUNION,idempotent_def,noids_def,FLOOKUP_DEF,rangevars_def] THEN
  `∃v. v IN FDOM s ∧ (s ' v = x)`
  by (POP_ASSUM MP_TAC THEN SRW_TAC [][FRANGE_DEF]) THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `Var v` MP_TAC) THEN
  SRW_TAC [][FLOOKUP_DEF] THEN
  IMP_RES_TAC subst_APPLY_id THEN
  SRW_TAC [][IN_DISJOINT] THEN
  METIS_TAC [] ) THEN
SRW_TAC [][noids_def,IN_DISJOINT,FLOOKUP_DEF,idempotent_def,subst_APPLY_id,rangevars_def] THEN1 (
  Induct_on `t` THEN SRW_TAC [][FLOOKUP_DEF] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  `s ' n IN FRANGE s` by (SRW_TAC [][FRANGE_DEF] THEN METIS_TAC []) THEN
  METIS_TAC [] ) THEN
Cases_on `v IN FDOM s` THEN SRW_TAC [][] THEN
`s ' v IN FRANGE s` by (SRW_TAC [][FRANGE_DEF] THEN METIS_TAC []) THEN
`v NOTIN (vars (s ' v))` by METIS_TAC [] THEN
Cases_on `s ' v` THEN FULL_SIMP_TAC (srw_ss()) []);

val wfs_FAPPLY_var = Q.store_thm(
"wfs_FAPPLY_var",
`wfs s ==> !v.v IN FDOM s ==> s ' v <> (Var v)`,
SRW_TAC [][wfs_no_cycles] THEN
`~vR s v v` by METIS_TAC [TC_SUBSET] THEN
POP_ASSUM MP_TAC THEN
Cases_on `s ' v` THEN
SRW_TAC [][vR_def,FLOOKUP_DEF]);

val TC_vR_vars_FRANGE = Q.store_thm(
"TC_vR_vars_FRANGE",
`∀u v. (vR s)^+ u v ⇒ v IN FDOM s ⇒ u IN BIGUNION (IMAGE vars (FRANGE s))`,
HO_MATCH_MP_TAC TC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [][vR_def] THEN1 (
  Cases_on `FLOOKUP s v` THEN FULL_SIMP_TAC (srw_ss()) [FLOOKUP_DEF] THEN
  Q.EXISTS_TAC `vars x` THEN SRW_TAC [][] THEN SRW_TAC [][FRANGE_DEF] THEN
  Q.EXISTS_TAC `s ' v` THEN SRW_TAC [][] THEN
  Q.EXISTS_TAC `v` THEN SRW_TAC [][] ) THEN
FIRST_X_ASSUM MATCH_MP_TAC THEN
IMP_RES_TAC TC_CASES2 THEN
FULL_SIMP_TAC (srw_ss()) [vR_def] THEN
FULL_SIMP_TAC (srw_ss()) [FLOOKUP_DEF] THEN
Cases_on `v IN FDOM s` THEN FULL_SIMP_TAC (srw_ss()) []);

val wfs_idempotent = Q.store_thm(
"wfs_idempotent",
`idempotent s ∧ noids s ⇒ wfs s`,
STRIP_TAC THEN IMP_RES_TAC idempotent_rangevars THEN
FULL_SIMP_TAC (srw_ss()) [rangevars_def] THEN
SRW_TAC [][wfs_no_cycles] THEN
SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
IMP_RES_TAC TC_vR_vars_FRANGE THEN
IMP_RES_TAC TC_CASES2 THEN
FULL_SIMP_TAC (srw_ss()) [vR_def,FLOOKUP_DEF] THEN
Cases_on `v IN FDOM s` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
RES_TAC THEN SRW_TAC [][] THEN
METIS_TAC [IN_DISJOINT]);

val _ = set_fixity "s_o_s"(Infixl 750);

val s_o_s_def = Define`
  s1 s_o_s s2 = FUN_FMAP (($'' s1) o ($'' s2 o Var)) (FDOM s1 ∪ FDOM s2)`;

val selfapp_def = Define`
  (selfapp s = ($'' s) o_f s)`;

val selfapp_eq_iter_APPLY = Q.store_thm(
"selfapp_eq_iter_APPLY",
`∀t. (selfapp s) '' t = s '' (s '' t)`,
Induct THEN SRW_TAC [][selfapp_def,FLOOKUP_DEF]);

val FDOM_selfapp = RWstore_thm(
"FDOM_selfapp",
`FDOM (selfapp s) = FDOM s`,
SRW_TAC [][selfapp_def]);

val selfapp_eq_s_o_s = Q.store_thm(
"selfapp_eq_s_o_s",
`selfapp s = s s_o_s s`,
SRW_TAC [][GSYM fmap_EQ,selfapp_def,s_o_s_def,FUN_FMAP_DEF,FUN_EQ_THM] THEN
Cases_on `x ∈ FDOM s` THEN SRW_TAC [][FUN_FMAP_DEF,NOT_FDOM_FAPPLY_FEMPTY,FLOOKUP_DEF]);

val IN_vars_APPLY = Q.store_thm(
"IN_vars_APPLY",
`∀t v. v IN vars (s '' t) ⇔ v NOTIN FDOM s ∧ v IN vars t ∨ ∃x. vR s v x ∧ x IN vars t`,
Induct THEN SRW_TAC [][vR_def] THEN
SRW_TAC [][FLOOKUP_DEF] THEN EQ_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
SRW_TAC [][] THEN METIS_TAC []);

val vR1_def = Define`
  vR1 s y x = vR s y x ∧ y NOTIN FDOM s`;

val vR_selfapp = Q.store_thm(
"vR_selfapp",
`vR (selfapp s) = vR1 s RUNION NRC (vR s) 2`,
SRW_TAC [][RUNION,FUN_EQ_THM,vR1_def,selfapp_def,vR_def,
           FLOOKUP_DEF,EQ_IMP_THM] THEN
FULL_SIMP_TAC bool_ss [TWO,ONE,NRC] THEN
Cases_on `x' IN FDOM s` THEN
FULL_SIMP_TAC (srw_ss()) [IN_vars_APPLY,vR_def,FLOOKUP_DEF] THEN
METIS_TAC []);

val vR1_selfapp = Q.store_thm(
"vR1_selfapp",
`vR1 (selfapp s) = vR1 s RUNION (vR s O vR1 s)`,
SRW_TAC [][FUN_EQ_THM,EQ_IMP_THM,vR1_def] THEN
FULL_SIMP_TAC (srw_ss()) [vR_selfapp,RUNION,O_DEF] THEN
FULL_SIMP_TAC bool_ss [TWO,ONE,NRC,vR1_def] THEN METIS_TAC []);

val FDOM_FUNPOW_selfapp = RWstore_thm(
"FDOM_FUNPOW_selfapp",
`FDOM (FUNPOW selfapp n s) = FDOM s`,
(FUNPOW_extends_mono |> Q.ISPEC `λs'. FDOM s' = FDOM s` |>
      SIMP_RULE (srw_ss()) [] |> MATCH_MP_TAC ) THEN
SRW_TAC [][]);

val NRC_2_IMP_TC_vR_selfapp = Q.store_thm(
"NRC_2_IMP_TC_vR_selfapp",
`∀n v u. NRC (vR s) (2* SUC n) v u ⇒ (vR (selfapp s))^+ v u`,
Induct THEN SRW_TAC [][] THEN1 (
  MATCH_MP_TAC TC_SUBSET THEN
  SRW_TAC [][vR_selfapp,RUNION] ) THEN
Cases_on `2 * SUC (SUC n)` THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) [NRC_SUC_RECURSE_LEFT,MULT_SUC,ADD1] THEN
Cases_on `n'` THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) [NRC_SUC_RECURSE_LEFT,ADD1] THEN
`2*n + 2 = n''` by DECIDE_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
RES_TAC THEN
`vR (selfapp s) z' u` by (
  SRW_TAC [][vR_selfapp,RUNION] THEN
  SIMP_TAC bool_ss [TWO,ONE,NRC] THEN
  METIS_TAC [] ) THEN
METIS_TAC [TC_RULES]);

val NRC_2_1_IMP_TC_vR_selfapp = Q.store_thm(
"NRC_2_1_IMP_TC_vR_selfapp",
`∀n v u. NRC (vR s) (2 * n) v u ∧ vR1 s w v ⇒ (vR (selfapp s))^+ w u`,
Induct THEN SRW_TAC [][] THEN1 (
  MATCH_MP_TAC TC_SUBSET THEN
  SRW_TAC [][vR_selfapp,RUNION] ) THEN
Cases_on `2 * SUC n` THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) [NRC_SUC_RECURSE_LEFT,ADD1] THEN
Cases_on `n'` THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) [NRC_SUC_RECURSE_LEFT,ADD1] THEN
`2*n = n''` by DECIDE_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
RES_TAC THEN
`vR (selfapp s) z' u` by (
  SRW_TAC [][vR_selfapp,RUNION] THEN
  SIMP_TAC bool_ss [TWO,ONE,NRC] THEN
  METIS_TAC [] ) THEN
IMP_RES_TAC TC_RULES);

val TC_vR_selfapp = Q.store_thm(
"TC_vR_selfapp",
`(vR (selfapp s))^+ v u ⇔ (∃n. NRC (vR s) (2 * (SUC n)) v u) ∨ (∃n u'. NRC (vR s) (2 * n) u' u ∧ vR1 s v u')`,
EQ_TAC THEN1 (
  MAP_EVERY Q.ID_SPEC_TAC [`u`,`v`] THEN
  HO_MATCH_MP_TAC TC_INDUCT THEN
  SRW_TAC [][vR_selfapp,RUNION] THENL [
    DISJ2_TAC THEN
    MAP_EVERY Q.EXISTS_TAC [`0`,`u`] THEN
    SRW_TAC [][],
    DISJ1_TAC THEN Q.EXISTS_TAC `0` THEN
    SRW_TAC [][],
    IMP_RES_TAC NRC_ADD_I THEN
    FULL_SIMP_TAC (srw_ss()++ARITH_ss) [GSYM LEFT_ADD_DISTRIB,GSYM ADD_SUC] THEN
    METIS_TAC [],
    Cases_on `2 * SUC n` THEN
    FULL_SIMP_TAC (srw_ss()) [NRC_SUC_RECURSE_LEFT,vR1_def,vR_def,FLOOKUP_DEF],
    IMP_RES_TAC NRC_ADD_I THEN
    FULL_SIMP_TAC (srw_ss()++ARITH_ss) [GSYM LEFT_ADD_DISTRIB,GSYM ADD_SUC] THEN
    METIS_TAC [],
    Cases_on `2 * n` THEN
    FULL_SIMP_TAC (srw_ss()) [NRC_SUC_RECURSE_LEFT,vR1_def,vR_def,FLOOKUP_DEF] THEN
    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) []
  ] ) THEN
SRW_TAC [][] THEN1
IMP_RES_TAC NRC_2_IMP_TC_vR_selfapp THEN
IMP_RES_TAC NRC_2_1_IMP_TC_vR_selfapp);

val wfs_selfapp = Q.store_thm(
"wfs_selfapp",
`wfs s ⇔ wfs (selfapp s)`,
SRW_TAC [][wfs_no_cycles,EQ_IMP_THM,TC_vR_selfapp] THEN
SPOSE_NOT_THEN STRIP_ASSUME_TAC THENL [
  Cases_on `2 * SUC n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  IMP_RES_TAC TC_eq_NRC THEN METIS_TAC [],
  Cases_on `2 * n` THEN FULL_SIMP_TAC (srw_ss()) [NRC_SUC_RECURSE_LEFT] THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [vR1_def,vR_def,FLOOKUP_DEF] THEN
  FULL_SIMP_TAC (srw_ss()) [],
  IMP_RES_TAC TC_eq_NRC THEN
  IMP_RES_TAC NRC_ADD_I THEN
  FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
  METIS_TAC []
]);

val vR_LRC_ALL_DISTINCT = Q.store_thm(
"vR_LRC_ALL_DISTINCT",
`wfs s ⇒ ∀ls v u. LRC (vR s) ls v u ⇒ ALL_DISTINCT ls`,
STRIP_TAC THEN Induct THEN SRW_TAC [][LRC_def] THEN1 (
  SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
  IMP_RES_TAC LRC_MEM_right THEN
  Cases_on `ls` THEN FULL_SIMP_TAC (srw_ss()) [LRC_def,wfs_no_cycles] THEN
  SRW_TAC [][] THEN1 (
    IMP_RES_TAC TC_SUBSET THEN RES_TAC) THEN
  RES_TAC THEN
  IMP_RES_TAC NRC_LRC THEN
  `NRC (vR s) (LENGTH p) h z` by METIS_TAC [] THEN
  Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [LRC_def] THEN
  SRW_TAC [][] THEN1 (
    NTAC 2 (IMP_RES_TAC TC_RULES) THEN
    RES_TAC ) THEN
  IMP_RES_TAC TC_eq_NRC THEN
  SRW_TAC [][] THEN
  NTAC 2 (IMP_RES_TAC TC_RULES) THEN
  RES_TAC) THEN RES_TAC);

val vR_LRC_FDOM = Q.store_thm(
"vR_LRC_FDOM",
`LRC (vR s) (h::t) v u ∧ MEM e t ⇒ e IN FDOM s`,
SRW_TAC [][] THEN IMP_RES_TAC LRC_MEM_right THEN
Cases_on `e IN FDOM s` THEN
FULL_SIMP_TAC (srw_ss()) [LRC_def,vR_def,FLOOKUP_DEF]);

val vR_LRC_bound = Q.store_thm(
"vR_LRC_bound",
`wfs s ∧ LRC (vR s) ls v u ⇒ LENGTH ls ≤ CARD (FDOM s) + 1`,
Cases_on `ls` THEN SRW_TAC [ARITH_ss][ADD1] THEN
IMP_RES_TAC vR_LRC_ALL_DISTINCT THEN
IMP_RES_TAC vR_LRC_FDOM THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
IMP_RES_TAC ALL_DISTINCT_CARD_LIST_TO_SET THEN
`set t SUBSET FDOM s` by SRW_TAC [][SUBSET_DEF] THEN
METIS_TAC [CARD_SUBSET,FDOM_FINITE]);

val idempotent_selfapp = Q.store_thm(
"idempotent_selfapp",
`idempotent s ⇔ (selfapp s = s)`,
SRW_TAC [][idempotent_def,EQ_IMP_THM,GSYM fmap_EQ,FUN_EQ_THM] THEN1 (
  Cases_on `x IN FDOM s` THEN1 (
    FIRST_X_ASSUM (Q.SPEC_THEN `Var x` MP_TAC) THEN
    SRW_TAC [][FLOOKUP_DEF,selfapp_def] ) THEN
  ASSUME_TAC FDOM_selfapp THEN
  SRW_TAC [][NOT_FDOM_FAPPLY_FEMPTY] ) THEN
Induct_on `t` THEN SRW_TAC [][] THEN
Cases_on `n IN FDOM s` THEN SRW_TAC [][FLOOKUP_DEF] THEN
FIRST_X_ASSUM (Q.SPEC_THEN `n` MP_TAC) THEN
SRW_TAC [][selfapp_def,o_f_DEF]);

val fixpoint_IMP_wfs = Q.store_thm(
"fixpoint_IMP_wfs",
`idempotent (FUNPOW selfapp n s) ∧ noids (FUNPOW selfapp n s) ⇒ wfs s`,
SRW_TAC [][] THEN IMP_RES_TAC wfs_idempotent THEN
POP_ASSUM MP_TAC THEN
REPEAT (POP_ASSUM (K ALL_TAC)) THEN
Induct_on `n` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [FUNPOW_SUC] THEN
IMP_RES_TAC wfs_selfapp THEN
RES_TAC);

val idempotent_substeq = Q.store_thm(
"idempotent_substeq",
`($'' s1 = $'' s2) ⇒ (idempotent s1 ⇔ idempotent s2)`,
SRW_TAC [][idempotent_def,EQ_IMP_THM]);

val vR_FUNPOW_selfapp_bound = Q.store_thm(
"vR_FUNPOW_selfapp_bound",
`∀n v u. vR (FUNPOW selfapp n s) v u ⇒ ∃m. 1 ≤ m ∧ NRC (vR s) m v u ∧ (v IN FDOM s ⇒ n ≤ m)`,
Induct THEN SRW_TAC [][] THEN1 (
  Q.EXISTS_TAC `1` THEN SRW_TAC [][] ) THEN
FULL_SIMP_TAC (srw_ss()) [FUNPOW_SUC,vR_selfapp,RUNION,vR1_def] THEN1 (
  RES_TAC THEN Q.EXISTS_TAC `m` THEN SRW_TAC [][] ) THEN
FULL_SIMP_TAC bool_ss [TWO,ONE,NRC] THEN
RES_TAC THEN IMP_RES_TAC NRC_ADD_I THEN
Q.EXISTS_TAC `m' + m` THEN SRW_TAC [][] THEN1
  DECIDE_TAC THEN
FULL_SIMP_TAC (srw_ss()) [vR_def,FLOOKUP_DEF] THEN
Cases_on `z IN FDOM s` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
DECIDE_TAC);

val idempotent_or_vR = Q.store_thm(
"idempotent_or_vR",
`idempotent s ∨ ∃u v. vR s v u ∧ v IN FDOM s`,
Cases_on `idempotent s` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [idempotent_def] THEN
Induct_on `t` THEN SRW_TAC [][] THENL [
  Cases_on `FLOOKUP s n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.EXISTS_TAC `n` THEN SRW_TAC [][vR_def] THEN
  (subst_APPLY_id |> Q.INST [`t`|->`x`] |> EQ_IMP_RULE |> snd |>
   CONTRAPOS |> IMP_RES_TAC) THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [],
  METIS_TAC [],
  METIS_TAC []
]);

val wfs_IMP_fixpoint = Q.store_thm(
"wfs_IMP_fixpoint",
`wfs s ⇒ ∃n. idempotent (FUNPOW selfapp n s) ∧ noids (FUNPOW selfapp n s)`,
STRIP_TAC THEN
`∀n. wfs (FUNPOW selfapp n s)`
by (MATCH_MP_TAC FUNPOW_extends_mono THEN
    SRW_TAC [][Once wfs_selfapp]) THEN
`∀n. noids (FUNPOW selfapp n s)`
by METIS_TAC [wfs_noids] THEN
SRW_TAC [][] THEN
SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
`∀n. ∃u v. vR (FUNPOW selfapp n s) v u ∧ v IN FDOM (FUNPOW selfapp n s)`
by METIS_TAC [idempotent_or_vR] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`∀n. ∃m v u. 1 ≤ m ∧ NRC (vR s) m v u ∧ n ≤ m`
by METIS_TAC [vR_FUNPOW_selfapp_bound] THEN
`∀n. ∃ls v u. LRC (vR s) ls v u ∧ n ≤ LENGTH ls`
by METIS_TAC [NRC_LRC] THEN
POP_ASSUM (Q.SPEC_THEN `CARD (FDOM s) + 2` STRIP_ASSUME_TAC) THEN
IMP_RES_TAC vR_LRC_bound THEN
DECIDE_TAC);

val wfs_iff_fixpoint = Q.store_thm(
"wfs_iff_fixpoint",
`wfs s ⇔ ∃n. idempotent (FUNPOW selfapp n s) ∧ noids (FUNPOW selfapp n s)`,
METIS_TAC [wfs_IMP_fixpoint,fixpoint_IMP_wfs]);

(*
val BIG_BAG_UNION_def = Define`
  BIG_BAG_UNION sob = λx. SIGMA (λb. b x) sob`;

val BIG_BAG_UNION_EMPTY = RWstore_thm(
"BIG_BAG_UNION_EMPTY",
`BIG_BAG_UNION {} = {||}`,
SRW_TAC [][BIG_BAG_UNION_def,SUM_IMAGE_THM,EMPTY_BAG,FUN_EQ_THM]);

val BIG_BAG_UNION_INSERT = Q.store_thm(
"BIG_BAG_UNION_INSERT",
`FINITE sob ⇒ (BIG_BAG_UNION (b INSERT sob) = b + BIG_BAG_UNION (sob DELETE b))`,
SRW_TAC [][BIG_BAG_UNION_def,SUM_IMAGE_THM,BAG_UNION,FUN_EQ_THM]);

val FINITE_BIG_BAG_UNION = Q.store_thm(
"FINITE_BIG_BAG_UNION",
`∀sob. FINITE sob ∧ (∀b. b IN sob ⇒ FINITE_BAG b) ⇒ FINITE_BAG (BIG_BAG_UNION sob)`,
SIMP_TAC bool_ss [GSYM AND_IMP_INTRO] THEN
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [][BIG_BAG_UNION_INSERT] THEN
FULL_SIMP_TAC (srw_ss()) [DELETE_NON_ELEMENT]);

val EMPTY_BIG_BAG_UNION = Q.store_thm(
"EMPTY_BIG_BAG_UNION",
`FINITE sob ⇒ ((BIG_BAG_UNION sob = {||}) ⇔ (∀b. b IN sob ⇒ (b = {||})))`,
Q.ID_SPEC_TAC `sob` THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [][BIG_BAG_UNION_INSERT,DELETE_NON_ELEMENT] THEN
SRW_TAC [][EQ_IMP_THM] THEN SRW_TAC [][]);

val BAG_IN_BIG_BAG_UNION = Q.store_thm(
"BAG_IN_BIG_BAG_UNION",
`∀sob. FINITE sob ⇒ (e <: BIG_BAG_UNION sob ⇔ ∃b. b IN sob ∧ e <: b)`,
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [][BIG_BAG_UNION_INSERT,DELETE_NON_ELEMENT,EQ_IMP_THM] THEN
METIS_TAC []);

val IMAGE_FAPPLY_FDOM = Q.store_thm(
"IMAGE_FAPPLY_FDOM",
`IMAGE ($' s) (FDOM s) = FRANGE s`,
SRW_TAC [][EXTENSION,FRANGE_DEF,EQ_IMP_THM] THEN METIS_TAC []);

val rangevarb_def = Define`
  rangevarb s = BIG_BAG_UNION (IMAGE varb (FRANGE s))`;

val FINITE_rangevarb = RWstore_thm(
"FINITE_rangevarb",
`FINITE_BAG (rangevarb s)`,
SRW_TAC [][rangevarb_def] THEN
HO_MATCH_MP_TAC FINITE_BIG_BAG_UNION THEN
SRW_TAC [][] THEN SRW_TAC [][]);

val domrangevarb_def = Define`
  domrangevarb s = BAG_FILTER (λv. v IN FDOM s) (rangevarb s)`;

val BAG_FILTER_EQ_EMPTY = Q.store_thm(
"BAG_FILTER_EQ_EMPTY",
`(BAG_FILTER P b = {||}) ⇔ ∀e. e <: b ⇒ ¬P e`,
SRW_TAC [][BAG_EXTENSION,BAG_INN_BAG_FILTER,BAG_IN,EQ_IMP_THM] THEN1 (
  FIRST_X_ASSUM (Q.SPECL_THEN [`1`,`e`] MP_TAC)
  THEN SRW_TAC [][] ) THEN
FIRST_X_ASSUM (Q.SPEC_THEN `e` MP_TAC) THEN
SRW_TAC [][] THEN
Cases_on `n < 1` THEN1 DECIDE_TAC THEN
(BAG_INN_LESS |> Q.SPECL [`b`,`e`,`n`,`1`] |> CONTRAPOS |> IMP_RES_TAC) THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`n = 1` by DECIDE_TAC THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) []);

val domrangevarb_idempotent = Q.store_thm(
"domrangevarb_idempotent",
`idempotent s ∧ noids s ⇔ (domrangevarb s = {||})`,
SRW_TAC []
[idempotent_rangevars,domrangevarb_def,rangevarb_def,
 BAG_FILTER_EQ_EMPTY,BAG_IN_BIG_BAG_UNION,EQ_IMP_THM] THEN1 (
 IMP_RES_TAC IN_varb_vars THEN
 RES_TAC THEN POP_ASSUM (Q.SPEC_THEN `vars x` MP_TAC) THEN
 SRW_TAC [][DISJOINT_DEF,EXTENSION] THEN METIS_TAC [] ) THEN
SRW_TAC [][DISJOINT_DEF,EXTENSION] THEN
Cases_on `x' IN vars x` THEN SRW_TAC [][] THEN
IMP_RES_TAC IN_varb_vars THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) []);
*)

(*

val selfapp_preserves_idempotent = Q.store_thm(
"selfapp_preserves_idempotent",
`idempotent s ∧ noids s ⇒ idempotent (selfapp s) ∧ noids (selfapp s)`,
SRW_TAC [][idempotent_def,noids_def,selfapp_eq_iter_APPLY] THEN
Cases_on `FLOOKUP (selfapp s) v` THEN
FULL_SIMP_TAC (srw_ss()) [FLOOKUP_DEF,selfapp_def] THEN
FIRST_X_ASSUM (Q.SPEC_THEN `Var v` MP_TAC) THEN
SRW_TAC [][FLOOKUP_DEF] THEN
FIRST_X_ASSUM (Q.SPEC_THEN `v` MP_TAC) THEN
SRW_TAC [][]);

this will be a consequence of wfs_IMP_fixpoint above ? ...
val repeated_selfapp_eq_apply_ts = Q.store_thm(
"repeated_selfapp_eq_apply_ts", MAYBE n HAS TO DEPEND ON THE TERM !!
`∃n. apply_ts s = subst_APPLY (FUNPOW selfapp n s)`,
Q_TAC SUFF_TAC `∀t.∃n. apply_ts s t = (FUNPOW selfapp n s) '' t`
THEN1 (
  SRW_TAC [][FUN_EQ_THM,SKOLEM_THM]
  SKOLEM_THM

FDOM s INTER BIGUNION (IMAGE vars (FRANGE s))

val wfs_IMP_fixpoint = Q.store_thm(
"wfs_IMP_fixpoint",
`wfs s ⇒ ∀t.∃n. (FUNPOW selfapp n s) '' t = apply_ts s t`

val FUNPOW_APPLY_apply_ts = Q.store_thm(
"FUNPOW_APPLY_apply_ts",
`(FUNPOW ($'' s) n t = apply_ts s t) ∧ m >= n ∧ wfs s ⇒
 (FUNPOW ($'' s) m t = apply_ts s t)`,
Induct_on `m` THEN SRW_TAC [][] THEN1 (
  Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] ) THEN
Cases_on `SUC m = n` THEN1 SRW_TAC [][] THEN
`m >= n` by FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
SRW_TAC [][FUNPOW_SUC] THEN
SRW_TAC [][apply_ts_eq_walkstar,subst_APPLY_walkstar]);

val FUNPOW_APPLY_pair = Q.store_thm(
"FUNPOW_APPLY_pair",
`FUNPOW ($'' s) n (Pair t1 t2) = Pair (FUNPOW ($'' s) n t1) (FUNPOW ($'' s) n t2)`,
Induct_on `n` THEN SRW_TAC [][FUNPOW_SUC] );

val wfs_IMP_fixpoint = Q.store_thm(
"wfs_IMP_fixpoint",
`wfs s ⇒ ∃n. idempotent (FUNPOW ($'' s) n)`
`wfs s ⇒ ∀t.∃n. FUNPOW ($'' s) n t = apply_ts s t`,
STRIP_TAC THEN HO_MATCH_MP_TAC apply_ts_ind THEN
SRW_TAC [][] THEN1 (
  Cases_on `FLOOKUP s t` THEN SRW_TAC [][] THENL [
    Q.EXISTS_TAC `0` THEN SRW_TAC [][],
    Q.EXISTS_TAC `SUC n` THEN SRW_TAC [][FUNPOW]
  ] ) THEN1 (
  SRW_TAC [][FUNPOW_APPLY_pair] THEN
  Q.EXISTS_TAC `MAX n n'` THEN
  SRW_TAC [][] THEN
  MATCH_MP_TAC (GEN_ALL FUNPOW_APPLY_apply_ts) THENL [
    Q.EXISTS_TAC `n`, Q.EXISTS_TAC `n'` ] THEN
  SRW_TAC [ARITH_ss][MAX_DEF] ) THEN
Q.EXISTS_TAC `0` THEN SRW_TAC [][]);

val fixpoint_IMP_wfs = Q.store_thm(
"fixpoint_IMP_wfs",
`(∀t.∃n. FUNPOW ($'' s) n t = FUNPOW ($'' s) (SUC n) t) ∧ noids s ⇒ wfs s`,
SRW_TAC [][] THEN
MATCH_MP_TAC wfs_idempotent THEN
SRW_TAC [][] THEN
SRW_TAC [][idempotent_def]

SRW_TAC [][wfs_no_cycles,noids_def] THEN
SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
TC_vR_vars_walkstar
FIRST_X_ASSUM (Q.SPEC_THEN `Var v` MP_TAC) THEN
SRW_TAC [][FUNPOW] THEN
IMP_RES_TAC TC_CASES1 THEN
FULL_SIMP_TAC (srw_ss()) [vR_def] THEN
Cases_on `FLOOKUP s v` THEN FULL_SIMP_TAC (srw_ss()) []

val FUNPOW_APPLY_term_depth = Q.store_thm(
"FUNPOW_APPLY_term_depth",
`∀n t. term_depth (FUNPOW ($'' s) n t) ≤ term_depth (FUNPOW ($'' s) (SUC n) t)`,
Induct THEN SRW_TAC [][] THEN1 (
  Induct_on `t` THEN SRW_TAC [ARITH_ss][] ) THEN
FULL_SIMP_TAC (srw_ss()) [FUNPOW]);

val FUNPOW_APPLY_NOT_FDOM = Q.store_thm(
"FUNPOW_APPLY_NOT_FDOM",
`v NOTIN FDOM s ⇒ (FUNPOW ($'' s) n (Var v) = Var v)`,
STRIP_TAC THEN Induct_on `n` THEN SRW_TAC [][FUNPOW,FLOOKUP_DEF]);

val NOT_FDOM_vars_APPLY = Q.store_thm(
"NOT_FDOM_vars_APPLY",
`v NOTIN FDOM s ⇒ v IN vars t ⇒ v IN vars (s '' t)`,
Induct_on `t` THEN SRW_TAC [][FLOOKUP_DEF] THEN
FULL_SIMP_TAC (srw_ss()) []);

val term_depth_APPLY = Q.store_thm(
"term_depth_APPLY",
`term_depth t ≤ term_depth (s '' t)`,
Induct_on `t` THEN SRW_TAC [ARITH_ss][]);

val APPLY_subterm = Q.store_thm(
"APPLY_subterm",
`v IN vars t ∧ t ≠ Var v ⇒ measure term_depth (s '' (Var v)) (s '' t)`,
Induct_on `t` THEN SRW_TAC [ARITH_ss][measure_thm] THEN
Cases_on `FLOOKUP s v` THEN SRW_TAC [ARITH_ss][] THEN
FULL_SIMP_TAC (srw_ss()) [measure_thm] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) []
THEN SRW_TAC [ARITH_ss][] THEN
Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) []
THEN SRW_TAC [ARITH_ss][]);

val wfs_iff_fixpoint_exists = Q.store_thm(
"wfs_iff_fixpoint_exists",
`wfs s ⇔ noids s ∧ ∀t.∃tt. OWHILE (λt. (s '' t) ≠ t) (subst_APPLY s) t = SOME tt`,
SRW_TAC [][EQ_IMP_THM] THEN1 METIS_TAC [wfs_noids] THENL [
  Q.EXISTS_TAC `walk* s t` THEN SRW_TAC [][OWHILE_def]

val substeq_def = Define`
  substeq s1 s2 = noids s1 ∧ noids s2 ∧ (∀t. s1 '' t = s2 '' t)`;

val substeq_refl = Q.store_thm(
"substeq_refl",
`noids s ⇒ substeq s s`,
SRW_TAC [][substeq_def]);

val substeq_sym = Q.store_thm(
"substeq_sym",
`substeq s1 s2 ⇒ substeq s2 s1`,
SRW_TAC [][substeq_def]);

val substeq_trans = Q.store_thm(
"substeq_trans",
`substeq s1 s2 ∧ substeq s2 s3 ⇒ substeq s1 s3`,
SRW_TAC [][substeq_def]);

val vR_substeq_mono = Q.store_thm(
"vR_substeq_mono",
`vR s1 u v ∧ substeq s1 s2 ⇒ vR s2 u v`,
SRW_TAC [][vR_def,substeq_def] THEN
Cases_on `FLOOKUP s1 v` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FIRST_X_ASSUM (Q.SPEC_THEN `Var v` MP_TAC) THEN
SRW_TAC [][] THEN
Cases_on `FLOOKUP s2 v` THEN FULL_SIMP_TAC (srw_ss()) [noids_def] THEN
METIS_TAC []);

val wfs_substeq_mono = Q.store_thm(
"wfs_substeq_mono",
`wfs s1 ∧ substeq s1 s2 ⇒ wfs s2`,
SRW_TAC [][wfs_def] THEN
Q_TAC SUFF_TAC `vR s1 = vR s2` THEN1 METIS_TAC [] THEN
SRW_TAC [][FUN_EQ_THM,EQ_IMP_THM] THEN
METIS_TAC [vR_substeq_mono,substeq_sym]);

val wfs_noids = Q.store_thm(
"wfs_noids",
`wfs s ⇒ noids s`,
SRW_TAC [][wfs_no_cycles,noids_def] THEN
SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
`vR s v v` by SRW_TAC [][vR_def] THEN
METIS_TAC [TC_SUBSET]);

val collapsable_eq_wfs = Q.store_thm(
"collapsable_eq_wfs", FALSE
`(∃si. idempotent si ∧ substeq si s) ⇔ wfs s`,
SRW_TAC [][EQ_IMP_THM] THEN1 (
  IMP_RES_TAC wfs_idempotent THEN
  METIS_TAC [wfs_substeq_mono,substeq_def] ) THEN
Q.EXISTS_TAC `collapse s` THEN
IMP_RES_TAC collapse_idempotent THEN

val FUNPOW_exists = Q.store_thm( (* similar to WHILE_INDUCTION *)
"FUNPOW_exists",
`∀R. WF R ∧ (∀n. ¬(P (FUNPOW f n x)) ⇒ R (FUNPOW f (SUC n) x) (FUNPOW f n x)) ⇒ ∃n. P (FUNPOW f n x)`,
SRW_TAC [][] THEN POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `x` THEN
HO_MATCH_MP_TAC (WF_INDUCTION_THM |> Q.SPEC `R` |> UNDISCH) THEN
SRW_TAC [][] THEN
Cases_on `P (FUNPOW f 0 x)` THEN1 METIS_TAC [] THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN RES_TAC THEN
Q_TAC SUFF_TAC `∃n. P (FUNPOW f n (f x))` THEN1 (
  STRIP_TAC THEN Q.EXISTS_TAC `SUC n` THEN SRW_TAC [][FUNPOW] ) THEN
POP_ASSUM MATCH_MP_TAC THEN SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPEC_THEN `SUC n` MP_TAC) THEN
SRW_TAC [][FUNPOW]);

val NRC_MUL_I = Q.store_thm(
"NRC_MUL_I",
`∀m n x y. NRC (NRC R m) n x y ⇒ NRC R (m * n) x y`,
Induct THEN Induct THEN SRW_TAC [][NRC] THEN1 (
  RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] ) THEN
RES_TAC THEN
IMP_RES_TAC NRC_1 THEN
IMP_RES_TAC NRC_ADD_I THEN
Q_TAC SUFF_TAC `SUC m * SUC n = 1 + m + SUC m * n`
THEN1 METIS_TAC [] THEN
SRW_TAC [ARITH_ss][MULT,ADD1]);
*)

(*
val collapsable_IMP_wfs = Q.store_thm(
"collapsable_IMP_wfs",
`∀s.(∃si. idempotent si ∧ (∀t. si '' t = s '' t)) ⇒ wfs s`,
SRW_TAC [][wfs_no_cycles]

val wfs_collapse = Q.store_thm(
"wfs_collapse",
`wfs s ==> wfs (collapse s)`,
SIMP_TAC (srw_ss()) [wfs_no_cycles] THEN
STRIP_TAC THEN
Q_TAC SUFF_TAC `!v u.(vR (collapse s))^+ v u ==> v <> u`
THEN1 METIS_TAC [] THEN
HO_MATCH_MP_TAC TC_STRONG_INDUCT THEN
SRW_TAC [][] THENL [
  Cases_on `u IN FDOM (collapse s)` THEN
  FULL_SIMP_TAC (srw_ss()) [vR_def,FLOOKUP_DEF] THEN
  `wfs s` by METIS_TAC [wfs_no_cycles] THEN
  `u IN FDOM s` by FULL_SIMP_TAC (srw_ss()) [collapse_def,FUN_FMAP_DEF] THEN
  FULL_SIMP_TAC (srw_ss()) [collapse_FAPPLY_eq_walkstar]

val subst_compose_exists = Q.prove(
`!s2 s1.?comp.!x.(subst_APPLY comp x = (subst_APPLY s2 (subst_APPLY s1 x)))`,
GEN_TAC THEN INDUCT_THEN fmap_INDUCT STRIP_ASSUME_TAC THENL [
  Q.EXISTS_TAC `s2` THEN Induct THEN SRW_TAC [][],
  SRW_TAC [][] THEN
  Q.EXISTS_TAC `comp |+ (x,s2 '' y)` THEN
  SRW_TAC [][] THEN
  Induct_on `x'` THEN SRW_TAC [][] THEN
  SRW_TAC [][FLOOKUP_UPDATE] THEN
  Q.PAT_ASSUM `!x.Z` (Q.SPEC_THEN `Var s` MP_TAC) THEN
  SRW_TAC [][]
]);

val subst_compose_def = new_specification
  ("subst_compose_def", ["subst_compose"],
   CONV_RULE (ONCE_DEPTH_CONV SKOLEM_CONV) subst_compose_exists);
set_fixity "oo" (Infixl 2000);
overload_on ("oo", ``subst_compose``);

val sunify_def = Define`
  (sunify (Var x) (Var y) = SOME if x = y then FEMPTY else (FEMPTY |+ (x, Var y))) /\
  (sunify (Var x) t2 = if x IN vars t2 then NONE else SOME (FEMPTY |+ (x,t2))) /\
  (sunify t1 (Var y) = if y IN vars t1 then NONE else SOME (FEMPTY |+ (y,t1))) /\
  (sunify (Pair t1a t1d) (Pair t2a t2d) =
    case sunify t1a t2a of NONE -> NONE ||
      SOME sa -> case sunify t1d t2d of NONE -> NONE ||
                   SOME sd -> SOME (sa oo sd)) /\
  (sunify (Const c1) (Const c2) = if c1 = c2 then SOME FEMPTY else NONE) /\
  (sunify _ _ = NONE)`;

val collapse_unify_eq_sunify = Q.store_thm(
"collapse_unify_eq_sunify",
`!s t1 t2 sx.wfs s /\ (unify s t1 t2 = SOME sx) ==>
   ?ss.(sunify t1 t2 = SOME ss) /\
       !t.((collapse sx) '' t = (ss oo s) '' t)`,
HO_MATCH_MP_TAC unify_ind THEN SRW_TAC [][] THEN
`wfs sx` by METIS_TAC [unify_uP,uP_def] THEN
Cases_on `walk s t1` THEN Cases_on `walk s t2` THEN
Q.PAT_ASSUM `unify X Y Z = D` MP_TAC THEN
SRW_TAC [][Once unify_def] THENL

`∀t1 t2. (s '' t1 = s '' t2) ⇒ (t1 = t2)`,
Induct THEN SRW_TAC [][] THENL [ false - x -> 3 and y -> 3
  Induct_on `t2` THEN FULL_SIMP_TAC (srw_ss()) []
Induct_on `t1` THEN SRW_TAC [][] THENL [
  Cases_on `FLOOKUP s n` THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
    Cases_on `t2` THEN FULL_SIMP_TAC (srw_ss()) []

val FUNPOW_extends_mono_cond = Q.store_thm(
"FUNPOW_extends_mono_cond",
`(∀x y. P x y ∧ Q x y ⇒ P (f x) (f y)) ⇒ ∀x y. (P x y ∧ Q x y ⇒ P (FUNPOW f n x) (FUNPOW f n y))`,
STRIP_TAC THEN Induct_on `n` THEN SRW_TAC [][FUNPOW_SUC]
);

`∀t1 t2. (λt1 t2. ∃v. (t1  = Var v) ∧ v IN vars t2 ∧ measure term_depth t1 t2) t1 t2 ⇒
(λt1 t2. ∃v. (t1  = Var v) ∧ v IN vars t2 ∧ measure term_depth t1 t2)
(FUNPOW ($'' s) n t1) (FUNPOW ($'' s) n t2)`,

val tmp =
FUNPOW_extends_mono |>
Q.INST_TYPE[`:'a`|->`:term`] |>
Q.INST[`P`|->`(λt1 t2. v IN vars t2 ∧ measure term_depth t1 t2)`,
       `f`|->`$'' s`]
|> SIMP_RULE (srw_ss()) [] |>
UNDISCH;

val [rtp] = hyp tmp;
val th = prove(rtp,
Induct THEN SRW_TAC [][] THEN
Cases_on `FLOOKUP s n` THEN SRW_TAC [][] THENL [
  FULL_SIMP_TAC (srw_ss()) [FLOOKUP_DEF] THEN
  METIS_TAC [NOT_FDOM_vars_APPLY],
  FULL_SIMP_TAC (srw_ss()) [measure_thm] THEN
  (term_depth_APPLY |> Q.GEN `t` |> Q.SPEC `y` |> MP_TAC) THEN
  SRW_TAC [ARITH_ss][],


`∀n. v IN vars t ∧ t ≠ Var v ⇒ (measure term_depth) (FUNPOW ($'' s) n (Var v)) (FUNPOW ($'' s) n t)`,
Induct THEN SRW_TAC [][] THEN1 (
  Induct_on `t` THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [measure_thm] ) THEN
SRW_TAC [][FUNPOW] THEN
Cases_on `FLOOKUP s v` THEN SRW_TAC [][] THEN1 (
  FULL_SIMP_TAC (srw_ss()) [measure_thm] THEN
  SRW_TAC [][GSYM FUNPOW] THEN
  SRW_TAC [][FUNPOW_SUC] THEN
  Q.MATCH_ABBREV_TAC `a < b` THEN
  Q_TAC SUFF_TAC `term_depth (FUNPOW ($'' s) n t) ≤ b` THEN1 (
    FULL_SIMP_TAC (srw_ss()++ARITH_ss) [Abbr`a`,Abbr`b`] ) THEN
  METIS_TAC [term_depth_APPLY] ) THEN
Q_TAC SUFF_TAC `x = (s '' (Var v))`
THEN1 METIS_TAC [APPLY_subterm]
SRW_TAC [][FUNPOW]



HO_MATCH_MP_TAC FUNPOW_extends_mono THEN
Induct THEN SRW_TAC [][]

∀t1 t2.(λt1 t2. ∃v. (t1 = Var v) ∧ v IN vars t2 ∧ term_depth) t1 t2 ⇒ (measure term_depth) (FUNPOW ($'' s) n t1) (FUNPOW ($'' s) n t2)`
HO_MATCH_MP_TAC FUNPOW_extends_mono THEN
Induct THEN SRW_TAC [][]

`(FUNPOW ($'' s) n (Var v) = FUNPOW ($'' s) n t) ∧ (t ≠ Var v) ⇒ v NOTIN vars t`,
STRIP_TAC THEN SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`term_depth (Var v) < term_depth t`
by (Induct_on `t` THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) []) THEN



Induct_on `n` THEN SRW_TAC [][] THEN
FIRST_X_ASSUM MATCH_MP_TAC THEN
SRW_TAC [][] THEN
HR
FULL_SIMP_TAC (srw_ss()) [FUNPOW] THEN
Cases_on `FLOOKUP s v` THEN FULL_SIMP_TAC (srw_ss()) [] THENL [


val FUNPOW_APPLY_preserves_type = Q.store_thm(
"FUNPOW_APPLY_preserves_type",
`∃FUNPOW ($'' s) n (Var v)

val rangevarb_recurses = save_thm(
"rangevarb_recurses",
COMMUTING_ITSET_RECURSES |> Q.ISPEC `rangevarb_acc` |>
SIMP_RULE (srw_ss()) [rangevarb_acc_def,ASSOC_BAG_UNION] |>
SIMP_RULE (srw_ss()) [COMM_BAG_UNION]);

val RELPOW_def = Define`
  (RELPOW R 0 = REMPTY) ∧
  (RELPOW R (SUC n) = R O (RELPOW R n))`;

val RELPOW1 = RWstore_thm(
"RELPOW1",
`RELPOW R 1 = R`,
SRW_TAC [][FUN_EQ_THM] THEN Cases_on `1` THEN
FULL_SIMP_TAC (srw_ss()) [RELPOW_def]);

val selfapp_rangevarb = Q.store_thm(
"selfapp_rangevarb",
`rangevarb s = rangevarb (selfapp s)`,
SRW_TAC [][rangevarb_def,selfapp_def,IMAGE_FAPPLY_FDOM]);

(∀b2. b2 IN sob2 ⇒ ∃b1. b1 IN sob1 ⇒ mlt1 R b2 b1) ⇒ (mlt1 R)^+ (BIG_BAG_UNION sob2) (BIG_BAG_UNION sob1)

val TC_vR_selfapp = Q.store_thm(
"TC_vR_selfapp",
`(vR (selfapp s))^+ v u ⇔ vR s v u ∧ v NOTIN FDOM s ∨ (∃n. NRC (vR s) (SUC (SUC n)) v u)`,
EQ_TAC THEN1 (
  MAP_EVERY Q.ID_SPEC_TAC [`u`,`v`] THEN
  HO_MATCH_MP_TAC TC_INDUCT THEN
  SRW_TAC [][vR_selfapp]
  THEN1 SRW_TAC [][]
  THEN1 (
    DISJ2_TAC THEN Q.EXISTS_TAC `0` THEN
    ASM_SIMP_TAC (srw_ss()) [] )
  THEN1 (
    DISJ2_TAC THEN Q.EXISTS_TAC `0` THEN
    ASM_SIMP_TAC (srw_ss()) [NRC] THEN
    METIS_TAC [] )
  THEN1 (
    IMP_RES_TAC NRC_1 THEN
    IMP_RES_TAC NRC_ADD_I THEN
    FULL_SIMP_TAC (srw_ss()++ARITH_ss) [GSYM ADD_SUC] THEN
    METIS_TAC [] )
  THEN1 (
    IMP_RES_TAC NRC_1 THEN
    IMP_RES_TAC NRC_ADD_I THEN
    FULL_SIMP_TAC (srw_ss()++ARITH_ss) [GSYM ADD_SUC,ADD_SYM] THEN
    METIS_TAC [] )
  THEN1 (
    IMP_RES_TAC NRC_ADD_I THEN
    FULL_SIMP_TAC (srw_ss()++ARITH_ss) [GSYM ADD_SUC] THEN
    METIS_TAC [] ) ) THEN
SRW_TAC [][] THEN1 (
  MATCH_MP_TAC TC_SUBSET THEN
  SRW_TAC [][vR_selfapp] ) THEN


SIMP_TAC (srw_ss()) [GSYM AND_IMP_INTRO] THEN
HO_MATCH_MP_TAC TC_INDUCT THEN
SRW_TAC [][] THEN1 (
  Cases_on `∃n. NRC (vR s) (SUC (SUC n)) y x'` THEN1 (
    FULL_SIMP_TAC (srw_ss()) [] THEN
    MATCH_MP_TAC TC_SUBSET THEN
    SRW_TAC [][vR_selfapp] THEN
    METIS_TAC [] ) THEN
  RES_TAC


  SRW_TAC [][] THEN
  IMP_RES_TAC TC_RULES THEN
  IMP_RES_TAC TC_RULES THEN
  `NRC (vR s) 2 y x'`
  by (Cases_on `2` THEN FULL_SIMP_TAC (srw_ss()) [NRC] THEN METIS_TAC []) THEN
  RES_TAC THEN FULL_SIMP_TAC (srw_ss()) []
  (Q.MATCH_ABBREV_TAC `R^+ a b` THEN
   METIS_TAC [TC_RULES]) ORELSE
  (`NRC (vR s) 2 y x'`
   by (Cases_on `2` THEN FULL_SIMP_TAC (srw_ss()) [NRC] THEN METIS_TAC []) THEN
   RES_TAC THEN FULL_SIMP_TAC (srw_ss()) []))
  SRW_TAC [][vR_selfapp] THEN
  SRW_TAC [][] THEN ((
    `NRC (vR s) 2 y x'`
    by (Cases_on `2` THEN FULL_SIMP_TAC (srw_ss()) [NRC] THEN METIS_TAC []) THEN
    RES_TAC THEN FULL_SIMP_TAC (srw_ss()) []) ORELSE
    METIS_TAC [TC_RULES]))

  ((
    Cases_on `y IN FDOM s` THEN
    FULL_SIMP_TAC (srw_ss()) [vR_def,FLOOKUP_DEF] THEN
    NO_TAC ) ORELSE
    METIS_TAC [TC_RULES])) THEN
SIMP_TAC (srw_ss()) [GSYM AND_IMP_INTRO] THEN
HO_MATCH_MP_TAC TC_INDUCT THEN
SRW_TAC [][]
STRIP_TAC
Q_TAC SUFF_TAC `(∀x y. (vR (selfapp s))^+ x y ⇒ (vR s)^+ x y) ∧
                (∀x y. (vR s)^+ x y ⇒ (vR (selfapp s))^+ x y)`
THEN1 (SRW_TAC [][FUN_EQ_THM] THEN METIS_TAC []) THEN
CONJ_TAC THEN1 (
  HO_MATCH_MP_TAC TC_INDUCT THEN
  SRW_TAC [][vR_selfapp] THEN
  METIS_TAC [TC_RULES]) THEN
HO_MATCH_MP_TAC TC_INDUCT THEN
SRW_TAC [][]
  ;


`(vR1 s RUNION NRC (vR s) (SUC (SUC 0))) y x ⇔ vR1 s y x ∨ ∃n. NRC (vR s) (SUC (SUC n)) y x`,
SRW_TAC [][vR1_def,RUNION,NRC,EQ_IMP_THM] THENL [
  SRW_TAC [][],
  DISJ2_TAC THEN
  Q.EXISTS_TAC `0` THEN
  Q.EXISTS_TAC `z` THEN
  SRW_TAC [][],
  SRW_TAC [][],
  false


val selfapp_rangevarb_mlt = Q.store_thm(
"selfapp_rangevarb_mlt",
`¬idempotent s ∧ noids s ⇒ (mlt1 (vR s))^+ (rangevarb (selfapp s)) (rangevarb s)`,
Q_TAC SUFF_TAC
`∀b. FINITE_BAG b ⇒ ∀s. (rangevarb s = b) ⇒ ¬idempotent s ∧ noids s ⇒
     (mlt1 (vR s))^+ (rangevarb (selfapp s)) (rangevarb s)`
THEN1 SRW_TAC [][] THEN
HO_MATCH_MP_TAC FINITE_BAG_INDUCT THEN
CONJ_TAC THEN1 (
  SRW_TAC [][rangevarb_def,EMPTY_BIG_BAG_UNION] THEN
  `~(DISJOINT (FDOM s) (BIGUNION (IMAGE vars (FRANGE s))))`
  by METIS_TAC [idempotent_rangevars] THEN
  FULL_SIMP_TAC (srw_ss()) [FRANGE_DEF] THEN
  Q_TAC SUFF_TAC `varb x = {||}` THEN1 (
    STRIP_TAC THEN
    `vars x = {}`
    by (SetCases_on `vars x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
        METIS_TAC [IN_varb_vars,NOT_IN_EMPTY_BAG,IN_INSERT]) THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [DISJOINT_EMPTY]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  Q.EXISTS_TAC `x` THEN SRW_TAC [][] THEN
  Q.EXISTS_TAC `x''` THEN SRW_TAC [][]) THEN
SRW_TAC [][]

  `varb b = {||}
  FIRST_X_ASSUM (Q.SPEC_THEN `varb b` MP_TAC) THEN
  SRW_TAC [][]
  SIMP_TAC (srw_ss()) [rangevarb_def,BIG_BAG_UNION_def,IMAGE_EMPTY] THEN
HO_MATCH_MP_TAC FINITE_INDUCT THEN
CONJ_TAC THEN1 (
  SRW_TAC [][] THEN
  `~(DISJOINT (FDOM s) (BIGUNION (IMAGE vars (FRANGE s))))`
  by METIS_TAC [idempotent_rangevars] THEN
  FULL_SIMP_TAC (srw_ss()) [FRANGE_DEF] THEN
  METIS_TAC [NOT_IN_EMPTY]) THEN
SRW_TAC [][]

  SRW_TAC [][idempotent_def,FRANGE_DEF,EXTENSION] THEN
  Induct_on `t` THEN FULL_SIMP_TAC (srw_ss()) [FLOOKUP_DEF]
SRW_TAC [][rangevarb_def,selfapp_def,IMAGE_FAPPLY_FDOM,IMAGE_COMPOSE] THEN
o_f_FRANGE
FULL_SIMP_TAC (srw_ss()) []

`∀s. wfs s ⇒ ∃n. idempotent (FUNPOW selfapp n s) ∧ noids (FUNPOW selfapp n s)`,
WHILE_INDUCTION |> Q.ISPECL [
`λs. ¬ idempotent s`,
`selfapp`,
`λss s. (mlt1 (vR s))^+ (domrangevarb ss) (domrangevarb s)`] |>
SIMP_RULE (srw_ss()) []

Q.EXISTS_TAC `λss s. (mlt1 (vR s))^+ (domrangevarb ss) (domrangevarb s)` THEN
SRW_TAC [][] THEN1 (
  SRW_TAC [][WF_EQ_WFP] THEN
  MATCH_MP_TAC WFP_RULES THEN
  SRW_TAC [][]
Q.EXISTS_TAC `inv_image (mlt1 (vR s))^+ domrangevarb` THEN
SRW_TAC [][] THEN1 (
  MATCH_MP_TAC WF_inv_image THEN
  MATCH_MP_TAC WF_TC THEN
  MATCH_MP_TAC WF_mlt1 THEN
  FULL_SIMP_TAC (srw_ss()) [wfs_def] ) THEN
SRW_TAC [][inv_image_def] THEN
SRW_TAC [][FUNPOW_SUC] THEN

Q_TAC SUFF_TAC
`∀s. ¬idempotent s ∧ noids s ⇒ (mlt1 (vR s))^+ (domrangevarb (selfapp s)) (domrangevarb s)`
METIS_TAC [FUNPOW_exists]
METIS_TAC [selfapp_rangevarb_mlt]);

val selfappR_def = Define`
  selfappR ss s = (mlt1 (vR s)^+)^+


val selfapp_rangevarb_mlt = Q.store_thm(
"selfapp_rangevarb_mlt",
`¬idempotent s ∧ noids s ⇒ (mlt1 (vR s))^+ (domrangevarb (selfapp s)) (domrangevarb s)`,

val sources_def = Define`
  sources s = {v | v IN FDOM s ∧ ∃u. (vR s)^+ v u }`;

val sources_SUBSET_FDOM = Q.store_thm(
"sources_SUBSET_FDOM",
`sources s SUBSET FDOM s`,
SRW_TAC [][SUBSET_DEF,sources_def]);

val sources_selfapp = Q.store_thm(
"sources_selfapp",
`wfs s ∧ sources s ≠ {} ⇒ (sources (selfapp s) PSUBSET sources s)`,
SRW_TAC [][sources_def,PSUBSET_DEF,SUBSET_DEF] THEN1 (
  IMP_RES_TAC TC_vR_selfapp THEN1 (
    Cases_on `2 * SUC n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    IMP_RES_TAC TC_eq_NRC THEN METIS_TAC [] ) THEN
  FULL_SIMP_TAC (srw_ss()) [vR1_def]) THEN
FULL_SIMP_TAC (srw_ss()) [EXTENSION,EQ_IMP_THM] THEN
Q.EXISTS_TAC `x` THEN SRW_TAC [][] THEN
SRW_TAC [][TC_vR_selfapp]

val (RTC_path_rules,RTC_path_ind,RTC_path_cases) = Hol_reln`
  (RTC_path R []) ∧
  (RTC_path R [y]) ∧
  (RTC_path R t ∧ R x y ⇒
   RTC_path R (x::y::t))`;

val RTC_path_strong_ind = save_thm(
"RTC_path_strong_ind",
IndDefLib.derive_strong_induction(RTC_path_rules, RTC_path_ind));

val vR_path_bound = Q.store_thm(
"vR_path_bound",
`wfs s ⇒ ∀ls. RTC_path (vR s) ls ⇒ LENGTH ls > 1 ⇒ LENGTH ls ≤ CARD (FDOM s)`,
STRIP_TAC THEN HO_MATCH_MP_TAC RTC_path_strong_ind THEN
SRW_TAC [][] THEN
Cases_on `ls` THEN FULL_SIMP_TAC (srw_ss()) []

val longest_path_def = Define`
  longest_path s = MAX_SET {n | ∃v u. NRC (vR s) n v u}`;

val NRC_vR_set = Q.store_thm(
"NRC_vR_set",
`wfs s ⇒ ∀n v u. NRC (vR s) n v u ⇒ ∃vs. vs SUBSET FDOM s ∧ (CARD vs = n) ∧ v NOTIN vs`,
STRIP_TAC THEN Induct THEN SRW_TAC [][] THEN1 (
  Q.EXISTS_TAC `{}` THEN SRW_TAC [][] ) THEN
FULL_SIMP_TAC (srw_ss()) [NRC] THEN
RES_TAC THEN
Q.EXISTS_TAC `z INSERT vs` THEN
FULL_SIMP_TAC (srw_ss()) [wfs_no_cycles] THEN
Cases_on `v = z` THEN1 (
  FULL_SIMP_TAC (srw_ss()) [] THEN
  IMP_RES_TAC TC_SUBSET THEN
  RES_TAC ) THEN

SRW_TAC [][] THENL [
  Cases_on `z IN FDOM s` THEN
  FULL_SIMP_TAC (srw_ss()) [vR_def,FLOOKUP_DEF],
  IMP_RES_TAC FDOM_FINITE THEN
  IMP_RES_TAC SUBSET_FINITE
  SRW_TAC [][CARD_INSERT]
FULL_SIMP_TAC (srw_ss()) [vR_def,wfs_no_cycles,FLOOKUP_DEF]


val wfs_max_path = Q.store_thm(
"wfs_max_path",
`wfs s ⇒ ∀n v u. NRC (vR s) n v u ⇒ n ≤ CARD (FDOM s)`,
STRIP_TAC THEN Induct THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [NRC] THEN
RES_TAC THEN
Cases_on `n = CARD (FDOM s)` THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) []

val vR_FUNPOW_selfapp = Q.store_thm(
"vR_FUNPOW_selfapp",
`∀n s v u. vR (FUNPOW selfapp n s) v u ⇔ ∃m. 1 ≤ m ∧ m ≤ n + 1 ∧ NRC (vR s) m v u ∧
                                            (m ≤ n ⇒ v NOTIN FDOM s)`,
Induct THEN SRW_TAC [][] THEN1 (
  SRW_TAC [][EQ_IMP_THM] THEN1 (
    Q.EXISTS_TAC `1` THEN SRW_TAC [][] ) THEN
  `m = 1` by DECIDE_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [] ) THEN
SRW_TAC [][EQ_IMP_THM,FUNPOW_SUC,vR_selfapp,RUNION] THENL [
  FULL_SIMP_TAC (srw_ss()) [vR1_def] THEN
  RES_TAC THEN Q.EXISTS_TAC `m` THEN SRW_TAC [][] THEN
  DECIDE_TAC,
  ...,
  Cases_on `m ≤ SUC n` THENL [
    SRW_TAC [][vR1_def] THEN
    DISJ1_TAC THEN
    Q.EXISTS_TAC `m` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    DECIDE_TAC,
    `m = SUC (SUC n)` by DECIDE_TAC THEN
    SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [NRC] THEN
    SIMP_TAC bool_ss [TWO,ONE,NRC] THEN


    FULL_SIMP_TAC (srw_ss()) []
  RES_TAC
  FULL_SIMP_TAC bool_ss [TWO,ONE,NRC] THEN
  Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1 (
    Q.EXISTS_TAC `2` THEN SRW_TAC [][] THEN
    SIMP_TAC bool_ss [TWO,ONE,NRC] THEN
    METIS_TAC [] ) THEN
  FULL_SIMP_TAC (srw_ss()) [FUNPOW_SUC] THEN
  FULL_SIMP_TAC (srw_ss()) [vR_selfapp,RUNION]
  RES_TAC THEN IMP_RES_TAC NRC_ADD_I THEN
  Q.EXISTS_TAC `m' + m` THEN SRW_TAC [][] THENL [
    DECIDE_TAC,
    FULL_SIMP_TAC (srw_ss()) [ADD1]


completeInduct_on `n` THEN SRW_TAC [][EQ_IMP_THM] THENL [
  Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1 (
    Q.EXISTS_TAC `1` THEN SRW_TAC [][] ) THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `n'` MP_TAC) THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [FUNPOW_SUC,vR_selfapp,RUNION] THEN1 (
    FULL_SIMP_TAC (srw_ss()) [vR1_def] THEN
    Q.EXISTS_TAC `m'` THEN SRW_TAC [][] THEN
    DECIDE_TAC ) THEN
  FULL_SIMP_TAC bool_ss [TWO,ONE,NRC] THEN
  RES_TAC
`∀n. vR (FUNPOW selfapp (SUC n) s) = vR1 s RUNION NRC (vR s) (2 * (SUC n))`,
Induct THEN SRW_TAC [][vR_selfapp] THEN
FULL_SIMP_TAC (srw_ss()) [vR_selfapp,FUNPOW_SUC,vR1_selfapp] THEN
FULL_SIMP_TAC (srw_ss()) [RUNION,FUN_EQ_THM,vR1_def,EQ_IMP_THM,vR_selfapp,O_DEF] THEN
SRW_TAC [][] THENL [
  RES_TAC THEN SRW_TAC [][] THEN

`¬idempotent (selfapp s) ⇒ ∃v u. NRC (vR s) 2 v u`,
SRW_TAC [][idempotent_def,selfapp_eq_iter_APPLY] THEN
Induct_on `t` THEN SRW_TAC [][] THEN1 (

`¬idempotent s ⇒ ∃v u. vR s v u ∧ v IN FDOM s`,
SRW_TAC [][idempotent_def,vR_def] THEN
REVERSE (Induct_on `t`) THEN SRW_TAC [][] THEN RES_TAC
THEN1 METIS_TAC [] THEN1 METIS_TAC [] THEN
Cases_on `FLOOKUP s n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
POP_ASSUM (K ALL_TAC) THEN
Induct_on `x` THEN SRW_TAC [][] THEN1 (
  MAP_EVERY Q.EXISTS_TAC [`n'`,`n`] THEN
  SRW_TAC [][] THEN
  Cases_on `FLOOKUP s n'` THEN
  FULL_SIMP_TAC (srw_ss()) [FLOOKUP_DEF] ) THEN
Cases_on `n IN FDOM s` THEN FULL_SIMP_TAC (srw_ss()) []

`idempotent (FUNPOW selfapp n s) ∨ ∃v u. NRC (vR s) n v u`,

`∀n. idempotent (FUNPOW selfapp n s) ∨ ∃v u. NRC (vR s) n v u`,
Induct THEN SRW_TAC [][] THEN1 (
  IMP_RES_TAC idempotent_selfapp THEN
  SRW_TAC [][FUNPOW_SUC] ) THEN
Cases_on `idempotent (FUNPOW selfapp (SUC n) s)` THEN
SRW_TAC [][NRC,idempotent_def,FUNPOW_SUC,selfapp_eq_iter_APPLY]

val vRn_def = Define`
  vRn s n y x = NRC (vR s) n y x ∧ y NOTIN FDOM s`;

val wfs_IMP_fixpoint = Q.store_thm(
"wfs_IMP_fixpoint",
`wfs s ⇒ ∃n. idempotent (FUNPOW selfapp n s) ∧ noids (FUNPOW selfapp n s)`,

SRW_TAC [][wfs_no_cycles,domrangevarb_idempotent] THEN
SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [domrangevarb_def,BAG_FILTER_EQ_EMPTY,rangevarb_def,BAG_IN_BIG_BAG_UNION] THEN
`∀n. wfs (FUNPOW selfapp n s)`
by (MATCH_MP_TAC FUNPOW_extends_mono THEN
    SRW_TAC [][Once wfs_selfapp]) THEN
`∀n. FDOM (FUNPOW selfapp n s) = FDOM s`
by ( (FUNPOW_extends_mono |> Q.ISPEC `λs'. FDOM s' = FDOM s` |>
      SIMP_RULE (srw_ss()) [] |> MATCH_MP_TAC ) THEN
     SRW_TAC [][]) THEN
FULL_SIMP_TAC (srw_ss()) [SKOLEM_THM,FORALL_AND_THM] THEN
TC_vR_selfapp
TC_vR_vars_FRANGE
SRW_TAC [][wfs_def,domrangevarb_idempotent] THEN
SRW_TAC [][BAG_EXTENSION]
WF_INDUCTION_THM |> Q.ISPEC `vR (s:subst)` |> UNDISCH |> HO_MATCH_MP_TAC
SRW_TAC [][domrangevarb_idempotent]

STRIP_TAC THEN
`∀n. wfs (FUNPOW selfapp n s)`
by (MATCH_MP_TAC FUNPOW_extends_mono THEN
    SRW_TAC [][Once wfs_selfapp]) THEN
`∀n. noids (FUNPOW selfapp n s)`
by METIS_TAC [wfs_noids] THEN
`∀n. FDOM (FUNPOW selfapp n s) = FDOM s`
by ( (FUNPOW_extends_mono |> Q.ISPEC `λs'. FDOM s' = FDOM s` |>
      SIMP_RULE (srw_ss()) [] |> MATCH_MP_TAC ) THEN
     SRW_TAC [][]) THEN
SRW_TAC [][] THEN HO_MATCH_MP_TAC FUNPOW_exists THEN
Q.EXISTS_TAC `inv_image (mlt1 (vR s)^+)^+ domrangevarb` THEN
CONJ_TAC THEN1 (
  MATCH_MP_TAC WF_inv_image THEN
  MATCH_MP_TAC WF_TC THEN
  MATCH_MP_TAC WF_mlt1 THEN
  MATCH_MP_TAC WF_TC THEN
  FULL_SIMP_TAC (srw_ss()) [wfs_def] ) THEN
Induct THEN FULL_SIMP_TAC (srw_ss()) [inv_image_def] THEN1 (
  STRIP_TAC THEN
  (domrangevarb_idempotent |> EQ_IMP_RULE |> snd |> CONTRAPOS |>
   SIMP_RULE (srw_ss()) [] |> IMP_RES_TAC)

*)

val _ = export_theory ();
