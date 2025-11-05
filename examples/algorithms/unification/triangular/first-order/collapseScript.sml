Theory collapse
Ancestors
  finite_map term pred_set subst walk walkstar
Libs
  ramanaLib

(* NB: collapsing a substitution means it's not triangular any more. The
 * intended method for applying triangular substitutions is to use walk*. The
 * relationship to directly applying a collapsed substitution proved here is
 * not intended as an implementation strategy, because it would destroy the
 * shared-tails benefits of using triangular substutions. *)

Definition collapse_def:
  collapse s = FUN_FMAP (\v.walkstar s (Var v)) (FDOM s)
End

Theorem collapse_APPLY_eq_walkstar:
 wfs s ==> !t.(collapse s ❜ t = walkstar s t)
Proof
STRIP_TAC THEN HO_MATCH_MP_TAC walkstar_ind THEN
SRW_TAC [][] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][collapse_def,FLOOKUP_DEF,FUN_FMAP_DEF] THEN
Cases_on `vwalk s n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [NOT_FDOM_vwalk,term_11,term_distinct]
QED

Theorem collapse_FAPPLY_eq_walkstar:
 wfs s ==> !v.v IN FDOM s ==> (collapse s ' v = walkstar s (Var v))
Proof
SRW_TAC [][collapse_def,FUN_FMAP_DEF]
QED

Theorem walkstar_unchanged:
 wfs s ==> !t.DISJOINT (vars t) (FDOM s) ==>
   (walkstar s t = t)
Proof
STRIP_TAC THEN HO_MATCH_MP_TAC walkstar_ind THEN
SRW_TAC [][] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][NOT_FDOM_vwalk]
QED

Theorem collapse_idempotent:
 wfs s ==> idempotent (collapse s)
Proof
METIS_TAC [walkstar_idempotent,idempotent_def,collapse_APPLY_eq_walkstar]
QED

Theorem idempotent_collapse:
 idempotent s ∧ noids s ==> (collapse s = s)
Proof
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
Q.PAT_X_ASSUM `walkstar X Y = Z` (fn th => ALL_TAC) THEN
SRW_TAC [][Once vwalk_def,FLOOKUP_DEF] THEN
Cases_on `s ' x` THEN SRW_TAC [][]
QED

Theorem walkstar_eq_idem_APPLY:
 wfs s ==> (idempotent s <=> (walkstar s = subst_APPLY s))
Proof
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
METIS_TAC [collapse_APPLY_eq_walkstar,subst_APPLY_FAPPLY]
QED

Theorem subst_APPLY_walkstar:
 wfs s ⇒ ∀t. s ❜ (walk* s t) = (walk* s t)
Proof
STRIP_TAC THEN HO_MATCH_MP_TAC apply_ts_ind THEN
SRW_TAC [][apply_ts_thm] THEN
Cases_on `FLOOKUP s t` THEN SRW_TAC [][]
QED

Theorem collapse_noids:
    wfs s ==> noids (collapse s)
Proof
  rw[noids_def,FLOOKUP_DEF] >>
  spose_not_then strip_assume_tac >>
  `v ∈ FDOM s` by fs[collapse_def] >>
  imp_res_tac collapse_FAPPLY_eq_walkstar >>
  rfs[] >>
  Cases_on`vwalk s v` >> rfs[] >> rw[] >>
  metis_tac[vwalk_no_cycles]
QED

Theorem wfs_collapse:
    wfs s ==> wfs (collapse s)
Proof
  metis_tac[collapse_idempotent,collapse_noids,wfs_idempotent]
QED

