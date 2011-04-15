open HolKernel boolLib bossLib Parse finite_mapTheory termTheory ramanaLib pred_setTheory substTheory walkTheory walkstarTheory;

val _ = new_theory "collapse";

val collapse_def = Define`
  collapse s = FUN_FMAP (\v.walkstar s (Var v)) (FDOM s)`;

val collapse_APPLY_eq_walkstar = Q.store_thm(
"collapse_APPLY_eq_walkstar",
`wfs s ==> !t.(collapse s '' t = walkstar s t)`,
STRIP_TAC THEN HO_MATCH_MP_TAC walkstar_ind THEN
SRW_TAC [][] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][collapse_def,FLOOKUP_DEF,FUN_FMAP_DEF] THEN
Cases_on `vwalk s n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [NOT_FDOM_vwalk,term_11,term_distinct]);

val collapse_FAPPLY_eq_walkstar = Q.store_thm(
"collapse_FAPPLY_eq_walkstar",
`wfs s ==> !v.v IN FDOM s ==> (collapse s ' v = walkstar s (Var v))`,
SRW_TAC [][collapse_def,FUN_FMAP_DEF]);

val walkstar_unchanged = Q.store_thm(
"walkstar_unchanged",
`wfs s ==> !t.DISJOINT (vars t) (FDOM s) ==>
   (walkstar s t = t)`,
STRIP_TAC THEN HO_MATCH_MP_TAC walkstar_ind THEN
SRW_TAC [][] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][NOT_FDOM_vwalk]);

val collapse_idempotent = Q.store_thm(
"collapse_idempotent",
`wfs s ==> idempotent (collapse s)`,
METIS_TAC [walkstar_idempotent,idempotent_def,collapse_APPLY_eq_walkstar]);

val idempotent_collapse = Q.store_thm(
"idempotent_collapse",
`idempotent s ∧ noids s ==> (collapse s = s)`,
STRIP_TAC THEN
`wfs s` by METIS_TAC [wfs_idempotent] THEN
`FDOM s = FDOM (collapse s)` by SRW_TAC [][collapse_def,FUN_FMAP_DEF] THEN
SRW_TAC [][GSYM fmap_EQ,FUN_EQ_THM] THEN
REVERSE (Cases_on `x IN FDOM s`) THEN1
  METIS_TAC [NOT_FDOM_FAPPLY_FEMPTY] THEN
`DISJOINT (FDOM s) (rangevars s)`
  by ((idempotent_rangevars |> EQ_IMP_RULE |> fst |> MATCH_MP_TAC) THEN
      SRW_TAC [][noids_def,FLOOKUP_DEF] THEN
      Cases_on `v IN FDOM (collapse s)` THEN SRW_TAC [][] THEN
      MATCH_MP_TAC (UNDISCH wfs_FAPPLY_var) THEN
      METIS_TAC []) THEN
`DISJOINT (FDOM s) (vars (s ' x))`
  by (FULL_SIMP_TAC (srw_ss()) [FRANGE_DEF,rangevars_def] THEN
      METIS_TAC []) THEN
`walkstar s (s ' x) = (s ' x)`
  by METIS_TAC [walkstar_unchanged,DISJOINT_SYM] THEN
Q_TAC SUFF_TAC `walkstar s (Var x) = walkstar s (s ' x)` THEN1
  METIS_TAC [collapse_FAPPLY_eq_walkstar] THEN
Q.PAT_ASSUM `walkstar X Y = Z` (fn th => ALL_TAC) THEN
SRW_TAC [][Once vwalk_def,FLOOKUP_DEF] THEN
Cases_on `s ' x` THEN SRW_TAC [][]);

val walkstar_eq_idem_APPLY = Q.store_thm(
"walkstar_eq_idem_APPLY",
`wfs s ==> (idempotent s <=> (walkstar s = subst_APPLY s))`,
STRIP_TAC THEN EQ_TAC THEN1
METIS_TAC [wfs_noids,idempotent_collapse,collapse_APPLY_eq_walkstar] THEN
STRIP_TAC THEN
Q_TAC SUFF_TAC `s = collapse s`
  THEN1 METIS_TAC [collapse_idempotent] THEN
`FDOM s = FDOM (collapse s)`
  by SRW_TAC [][collapse_def,FUN_FMAP_DEF] THEN
SRW_TAC [][GSYM fmap_EQ,FUN_EQ_THM] THEN
REVERSE (Cases_on `x IN FDOM s`) THEN1
  METIS_TAC [NOT_FDOM_FAPPLY_FEMPTY] THEN
METIS_TAC [collapse_APPLY_eq_walkstar,subst_APPLY_FAPPLY]);

val subst_APPLY_walkstar = Q.store_thm(
"subst_APPLY_walkstar",
`wfs s ⇒ ∀t. s '' (walk* s t) = (walk* s t)`,
STRIP_TAC THEN HO_MATCH_MP_TAC apply_ts_ind THEN
SRW_TAC [][apply_ts_thm] THEN
Cases_on `FLOOKUP s t` THEN SRW_TAC [][] );

val _ = export_theory ();
