open HolKernel boolLib bossLib ramanaLib Parse stringTheory arithmeticTheory finite_mapTheory pred_setTheory bagTheory pairTheory termTheory relationTheory prim_recTheory unifDefTheory substTheory walkTheory walkstarTheory

val _ = new_theory "unifProps"
val _ = metisTools.limit :=  { time = NONE, infs = SOME 5000 }

val vwalk_irrelevant_FUPDATE = Q.store_thm(
"vwalk_irrelevant_FUPDATE",
`wfs (s|+(vx,tx)) /\ vx NOTIN FDOM s ==>
  !v.~(vR s)^* vx v ==> (vwalk (s|+(vx,tx)) v = vwalk s v)`,
STRIP_TAC THEN
`wfs s` by METIS_TAC [wfs_SUBMAP,SUBMAP_FUPDATE_EQN] THEN
HO_MATCH_MP_TAC vwalk_ind THEN
SRW_TAC [][] THEN
`vx <> v` by METIS_TAC [RTC_REFL] THEN
Cases_on `FLOOKUP s v` THENL [
  `v NOTIN FDOM s /\ v NOTIN FDOM (s|+(vx,tx))`
     by (POP_ASSUM MP_TAC THEN SRW_TAC [][FLOOKUP_DEF]) THEN
  METIS_TAC [DISCH_ALL NOT_FDOM_vwalk,term_11],
  Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
    `vR s n v` by FULL_SIMP_TAC (srw_ss()) [vR_def] THEN
    `~(vR s)^* vx n`
       by METIS_TAC [RTC_SUBSET,RTC_TRANSITIVE,transitive_def] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][Once vwalk_def,SimpLHS,FLOOKUP_UPDATE] THEN
    SRW_TAC [][Once vwalk_def,SimpRHS],
    SRW_TAC [][Once vwalk_def,SimpLHS,FLOOKUP_UPDATE] THEN
    SRW_TAC [][Once vwalk_def,SimpRHS],
    SRW_TAC [][Once vwalk_def,SimpLHS,FLOOKUP_UPDATE] THEN
    SRW_TAC [][Once vwalk_def,SimpRHS]
  ]
]);

val vR_SUBMAP = Q.prove(
`s SUBMAP sx ==> vR s u v ==> vR sx u v`,
Cases_on `FLOOKUP s v` THEN
SRW_TAC [][vR_def] THEN
`FLOOKUP sx v = SOME x` by METIS_TAC [FLOOKUP_SUBMAP] THEN
SRW_TAC [][]);

val TC_vR_SUBMAP = Q.store_thm(
"TC_vR_SUBMAP",
`s SUBMAP sx ==> !u v.(vR s)^+ u v ==> (vR sx)^+ u v`,
STRIP_TAC THEN HO_MATCH_MP_TAC TC_INDUCT THEN
SRW_TAC [][] THEN1 METIS_TAC [TC_SUBSET,vR_SUBMAP] THEN
METIS_TAC [TC_RULES]);

val vwalk_FUPDATE_var = Q.store_thm(
"vwalk_FUPDATE_var",
`wfs (s|+(v1,Var v2)) /\ v1 NOTIN FDOM s ==>
   (vwalk (s|+(v1,Var v2)) v2 = vwalk s v2)`,
SRW_TAC [][] THEN
Q_TAC SUFF_TAC `~(vR s)^* v1 v2`
  THEN1 METIS_TAC [vwalk_irrelevant_FUPDATE] THEN
SRW_TAC [][RTC_CASES_TC] THENL [
  SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
  `vR (s|+(v1,Var v2)) v1 v1` by SRW_TAC [] [vR_def,FLOOKUP_UPDATE] THEN
  METIS_TAC [wfs_no_cycles,TC_SUBSET],
  `s SUBMAP (s|+(v1,Var v2))` by METIS_TAC [SUBMAP_FUPDATE_EQN] THEN
  Q.PAT_ASSUM `wfs Z` MP_TAC THEN
  SRW_TAC [][wfs_no_cycles] THEN
  POP_ASSUM (Q.SPEC_THEN `v2` MP_TAC) THEN
  SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
  `(vR (s|+(v1,Var v2)))^+ v1 v2` by METIS_TAC [TC_vR_SUBMAP] THEN
  `vR (s|+(v1,Var v2)) v2 v1` by SRW_TAC [][vR_def,FLOOKUP_UPDATE] THEN
  METIS_TAC [TC_RULES]
]);

val walkstar_extend = Q.store_thm(
"walkstar_extend",
`wfs s1 /\ wfs (s|+(vx,tx)) /\ vx NOTIN FDOM s /\
 (walkstar s1 (Var vx) = walkstar s1 (walkstar s tx)) ==>
   !t.(walkstar s1 (walkstar (s|+(vx,tx)) t) = walkstar s1 (walkstar s t))`,
STRIP_TAC THEN
`s SUBMAP (s|+(vx,tx)) /\ wfs s` by METIS_TAC [wfs_SUBMAP,SUBMAP_FUPDATE_EQN] THEN
HO_MATCH_MP_TAC (Q.INST[`s`|->`s|+(vx,tx)`]walkstar_ind) THEN
SRW_TAC [][] THEN
Cases_on `t` THEN SRW_TAC [][] THEN
Q.SPECL_THEN [`n`,`s`] MP_TAC
  (Q.INST[`sx`|->`s|+(vx,tx)`] (UNDISCH vwalk_SUBMAP)) THEN
Cases_on `vwalk s n` THEN SRW_TAC [][] THEN
Q.PAT_ASSUM `!v5 v6.Z` MP_TAC THEN
Cases_on `vwalk (s|+(vx,tx)) n'` THEN
SRW_TAC [][] THENL [
  Cases_on `n' = vx` THENL [
    Q.PAT_ASSUM `vwalk (s|+(vx,tx)) n' = Var n''` MP_TAC THEN
    SRW_TAC [][Once(DISCH_ALL vwalk_def),SimpLHS,FLOOKUP_UPDATE] THEN
    POP_ASSUM MP_TAC THEN
    Cases_on `tx` THEN SRW_TAC [][] THEN
    `vwalk s n''' = Var n''` by METIS_TAC [vwalk_FUPDATE_var] THEN
    Q.PAT_ASSUM `walkstar s1 X = walkstar s1 Y` MP_TAC THEN
    SRW_TAC [][NOT_FDOM_vwalk],
    `n' NOTIN FDOM s` by METIS_TAC [vwalk_to_var] THEN
    Q.PAT_ASSUM `vwalk (s|+(vx,tx)) n' = Var n''` MP_TAC THEN
    SRW_TAC [][Once(DISCH_ALL vwalk_def),SimpLHS,FLOOKUP_UPDATE,FLOOKUP_DEF]
  ],
  `walkstar s (Var vx) = Var vx` by SRW_TAC [][NOT_FDOM_vwalk] THEN
  `n' NOTIN FDOM s` by METIS_TAC [vwalk_to_var] THEN
  `n' = vx`
     by (Q.PAT_ASSUM `vwalk (s|+(vx,tx)) n' = Z` MP_TAC THEN
         SRW_TAC [][Once(DISCH_ALL vwalk_def),SimpLHS,
                    FLOOKUP_UPDATE,FLOOKUP_DEF]) THEN
  Q.PAT_ASSUM `vwalk (s|+(vx,tx)) n' = Z` MP_TAC THEN
  SRW_TAC [][Once(DISCH_ALL vwalk_def),SimpLHS,FLOOKUP_UPDATE] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  POP_ASSUM MP_TAC THEN
  Cases_on `tx` THEN SRW_TAC [][] THEN
  Q.PAT_ASSUM `walkstar s1 (Var X) = walkstar s1 Y` MP_TAC
  THEN SRW_TAC [][] THEN
  `vwalk s n'' = Pair t t0` by METIS_TAC [vwalk_FUPDATE_var] THEN
  SRW_TAC [][],
  `walkstar s (Var vx) = Var vx` by SRW_TAC [][NOT_FDOM_vwalk] THEN
  `n' NOTIN FDOM s` by METIS_TAC [vwalk_to_var] THEN
  `n' = vx`
     by (Q.PAT_ASSUM `vwalk (s|+(vx,tx)) n' = Z` MP_TAC THEN
         SRW_TAC [][Once(DISCH_ALL vwalk_def),SimpLHS,
                    FLOOKUP_UPDATE,FLOOKUP_DEF]) THEN
  Q.PAT_ASSUM `vwalk (s|+(vx,tx)) n' = Z` MP_TAC THEN
  SRW_TAC [][Once(DISCH_ALL vwalk_def),SimpLHS,FLOOKUP_UPDATE] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  POP_ASSUM MP_TAC THEN
  Cases_on `tx` THEN SRW_TAC [][] THEN
  Q.PAT_ASSUM `walkstar s1 (Var X) = walkstar s1 Y` MP_TAC
  THEN SRW_TAC [][] THEN
  Q.MATCH_ASSUM_RENAME_TAC `vwalk X n'' = Const c` ["X"] THEN
  `vwalk s n'' = Const c` by METIS_TAC [vwalk_FUPDATE_var] THEN
  Q.SPECL_THEN [`n''`,`s`] MP_TAC
    (Q.INST[`sx`|->`s1`] (UNDISCH vwalk_SUBMAP)) THEN
  SRW_TAC [][]
]);

val wex = Q.prove(
`wfs s1 /\ wfs (s|+(vx,tx)) /\
 (walkstar s1 (walk* s (Var vx)) = walkstar s1 (walkstar s tx)) /\ vx NOTIN FDOM s
 ==> !t.(walkstar s1 (walkstar (s|+(vx,tx)) t) = walkstar s1 (walkstar s t))`,
STRIP_TAC THEN
`wfs s` by METIS_TAC [wfs_SUBMAP,SUBMAP_FUPDATE_EQN] THEN
FULL_SIMP_TAC (srw_ss()) [NOT_FDOM_vwalk] THEN
METIS_TAC [walkstar_extend])

val unify_mgu = Q.store_thm(
"unify_mgu",
`!s t1 t2 sx s2. wfs s ∧ (unify s t1 t2 = SOME sx) ∧
  wfs s2 /\ (walk* s2 (walk* s t1) = walk* s2 (walk* s t2)) ==>
 !t.(walk* s2 (walk* sx t) = walk* s2 (walk* s t))`,
HO_MATCH_MP_TAC unify_ind THEN SRW_TAC [][] THEN
`wfs sx` by METIS_TAC [unify_uP,uP_def] THEN
Cases_on `walk s t1` THEN Cases_on `walk s t2` THEN
Q.PAT_ASSUM `unify X Y Z = D` MP_TAC THEN
SRW_TAC [][Once unify_def] THENL [
  METIS_TAC [walkstar_walk,wex,walk_to_var],
  METIS_TAC [walkstar_walk,wex,walk_to_var],
  METIS_TAC [walkstar_walk,wex,walk_to_var],
  METIS_TAC [walkstar_walk,wex,walk_to_var],
  `walk* s2 (walk* s (walk s t1)) = walk* s2 (walk* s (walk s t2))`
    by METIS_TAC [walkstar_walk] THEN
  Cases_on `unify s t' t''` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  `wfs x` by METIS_TAC [unify_uP,uP_def] THEN SRW_TAC [][] THEN
  MAP_EVERY (fn x => Q.PAT_ASSUM x ASSUME_TAC)
    [`wfs s`,`unify x Y Z = SOME sx`,`wfs s2`,`walk s t1 = X`,`walk s t2 = X`] THEN
  FULL_SIMP_TAC (srw_ss()) [],
  METIS_TAC [walkstar_walk,wex,walk_to_var]
])

val unify_mgu_FEMPTY = Q.store_thm(
"unify_mgu_FEMPTY",
`(unify FEMPTY t1 t2 = SOME sx) ==>
 !s.wfs s /\ (walkstar s t1 = walkstar s t2) ==>
   ?s'.!t.(walkstar s' (walkstar sx t) = walkstar s t)`,
METIS_TAC [unify_mgu,wfs_FEMPTY,walkstar_FEMPTY])

val walkstar_walk_SUBMAP = Q.store_thm(
"walkstar_walk_SUBMAP",
`s SUBMAP sx /\ wfs sx ==>
  (walkstar sx t = walkstar sx (walk s t))`,
METIS_TAC [walkstar_SUBMAP,walkstar_walk,wfs_SUBMAP])

val unify_unifier = Q.store_thm(
"unify_unifier",
`wfs s ∧ (unify s t1 t2 = SOME sx) ⇒
 wfs sx ∧ s SUBMAP sx ∧ (walk* sx t1 = walk* sx t2)`,
Q_TAC SUFF_TAC
`!s t1 t2 sx.wfs s /\ (unify s t1 t2 = SOME sx) ==>
   wfs sx ∧ s SUBMAP sx ∧ (walk* sx t1 = (walk* sx t2))`
THEN1 METIS_TAC [] THEN
HO_MATCH_MP_TAC unify_ind THEN SRW_TAC [][] THEN
`wfs sx /\ s SUBMAP sx` by METIS_TAC [unify_uP,uP_def] THEN
Q.PAT_ASSUM `unify s t1 t2 = SOME sx` MP_TAC THEN
Cases_on `walk s t1` THEN Cases_on `walk s t2` THEN
SRW_TAC [][Once unify_def] THENL [
  Cases_on `t1` THEN Cases_on `t2` THEN
  FULL_SIMP_TAC (srw_ss()) [walk_def],
  Q.MATCH_ABBREV_TAC `walkstar sx t1 = walkstar sx t2` THEN
  `(walkstar sx t1 = walkstar sx (walk s t1)) /\
   (walkstar sx t2 = walkstar sx (walk s t2))`
     by METIS_TAC [walkstar_walk_SUBMAP] THEN
  MP_TAC (Q.INST[`t`|->`t1`]walk_SUBMAP) THEN
  MP_TAC (Q.INST[`t`|->`t2`]walk_SUBMAP) THEN
  Q.UNABBREV_TAC `sx` THEN
  REPEAT(SRW_TAC [][Once vwalk_def,FLOOKUP_UPDATE]),
  Q.MATCH_ABBREV_TAC `walkstar sx t1 = walkstar sx t2` THEN
  `(walkstar sx t1 = walkstar sx (walk s t1)) /\
   (walkstar sx t2 = walkstar sx (walk s t2))`
     by METIS_TAC [walkstar_walk_SUBMAP] THEN
  MP_TAC (Q.INST[`t`|->`t1`]walk_SUBMAP) THEN
  MP_TAC (Q.INST[`t`|->`t2`]walk_SUBMAP) THEN
  Q.UNABBREV_TAC `sx` THEN
  REPEAT(SRW_TAC [][Once vwalk_def,FLOOKUP_UPDATE]),
  Q.MATCH_ABBREV_TAC `walkstar sx t1 = walkstar sx t2` THEN
  `(walkstar sx t1 = walkstar sx (walk s t1)) /\
   (walkstar sx t2 = walkstar sx (walk s t2))`
     by METIS_TAC [walkstar_walk_SUBMAP] THEN
  MP_TAC (Q.INST[`t`|->`t1`]walk_SUBMAP) THEN
  MP_TAC (Q.INST[`t`|->`t2`]walk_SUBMAP) THEN
  Q.UNABBREV_TAC `sx` THEN
  REPEAT(SRW_TAC [][Once(DISCH_ALL vwalk_def),FLOOKUP_UPDATE]),
  Q.MATCH_ABBREV_TAC `walkstar sx t1 = walkstar sx t2` THEN
  `(walkstar sx t1 = walkstar sx (walk s t1)) /\
   (walkstar sx t2 = walkstar sx (walk s t2))`
     by METIS_TAC [walkstar_walk_SUBMAP] THEN
  MP_TAC (Q.INST[`t`|->`t1`]walk_SUBMAP) THEN
  MP_TAC (Q.INST[`t`|->`t2`]walk_SUBMAP) THEN
  Q.UNABBREV_TAC `sx` THEN
  REPEAT(SRW_TAC [][Once(DISCH_ALL vwalk_def),FLOOKUP_UPDATE]),
  `(walkstar sx t1 = walkstar sx (walk s t1)) /\
   (walkstar sx t2 = walkstar sx (walk s t2))`
     by METIS_TAC [walkstar_walk_SUBMAP] THEN
  Cases_on `unify s t t'` THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  `wfs x /\ x SUBMAP sx` by METIS_TAC [unify_uP,uP_def] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  METIS_TAC [walkstar_SUBMAP],
  Q.MATCH_ABBREV_TAC `walkstar sx t1 = walkstar sx t2` THEN
  `(walkstar sx t1 = walkstar sx (walk s t1)) /\
   (walkstar sx t2 = walkstar sx (walk s t2))`
     by METIS_TAC [walkstar_walk_SUBMAP] THEN
  MP_TAC (Q.INST[`t`|->`t1`]walk_SUBMAP) THEN
  MP_TAC (Q.INST[`t`|->`t2`]walk_SUBMAP) THEN
  Q.UNABBREV_TAC `sx` THEN
  REPEAT(SRW_TAC [][Once(DISCH_ALL vwalk_def),FLOOKUP_UPDATE]),
  Cases_on `t1` THEN Cases_on `t2` THEN
  FULL_SIMP_TAC (srw_ss()) [walk_def]
])

val walk_to_var_NOT_FDOM = Q.prove(
`wfs s ∧ (walk s t = Var v) ⇒ v ∉ FDOM s`,
METIS_TAC [walk_to_var])

val vars_measure = Q.store_thm(
"vars_measure",
`v ∈ vars t ∧ (∀w. t ≠ Var w) ∧ wfs s ⇒
 measure (pair_count o (walk* s)) (Var v) t`,
Induct_on `t` THEN SRW_TAC [][] THEN
Q.MATCH_ASSUM_RENAME_TAC `v ∈ vars tt` [] THEN
Q.PAT_ASSUM `wfs s` ASSUME_TAC THEN
Cases_on `tt` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) [measure_thm])

val oc_subterm_neq = Q.store_thm(
"oc_subterm_neq",
`oc s t v ∧ (∀w. t ≠ Var w) ∧ wfs s ∧ wfs s2 ⇒
 walk* s2 (Var v) ≠ walk* s2 (walk* s t)`,
STRIP_TAC THEN
`v ∈ vars (walk* s t)` by METIS_TAC [oc_eq_vars_walkstar,IN_DEF] THEN
`∀w. (walk* s t) ≠ Var w` by (Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
IMP_RES_TAC vars_measure THEN
SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [measure_thm])

val eqs_unify = Q.store_thm(
"eqs_unify",
`wfs s ∧ wfs s2 ∧ (walk* s2 (walk* s t1) = walk* s2 (walk* s t2)) ⇒
 ∃sx. unify s t1 t2 = SOME sx`,
Q_TAC SUFF_TAC
`∀s t1 t2. wfs s ∧ wfs s2 ∧ (walk* s2 (walk* s t1) = walk* s2 (walk* s t2)) ⇒
 ∃sx. unify s t1 t2 = SOME sx` THEN1 METIS_TAC [] THEN
HO_MATCH_MP_TAC unify_ind THEN SRW_TAC [][] THEN
`(walk* s t1 = walk* s (walk s t1)) ∧
 (walk* s t2 = walk* s (walk s t2))`
by METIS_TAC [walkstar_walk] THEN
MAP_EVERY Cases_on [`walk s t1`,`walk s t2`] THEN
Q.PAT_ASSUM `wfs s2` ASSUME_TAC THEN
Q.PAT_ASSUM `wfs s` ASSUME_TAC THEN
IMP_RES_TAC walk_to_var_NOT_FDOM THEN
FULL_SIMP_TAC (srw_ss()) [NOT_FDOM_vwalk] THEN
ASM_SIMP_TAC (srw_ss()) [Once unify_def] THEN1 (
  Q.MATCH_ASSUM_RENAME_TAC `walk s X = Pair c1 c2` ["X"] THEN
  (oc_subterm_neq |> CONTRAPOS |>
   Q.INST [`v`|->`n`,`t`|->`Pair c1 c2`] |>
   MP_TAC) THEN
  ASM_SIMP_TAC (srw_ss()) [] )
THEN1 (
  Q.MATCH_ASSUM_RENAME_TAC `walk s X = Pair c1 c2` ["X"] THEN
  (oc_subterm_neq |> CONTRAPOS |>
   Q.INST [`v`|->`n`,`t`|->`Pair c1 c2`] |>
   MP_TAC) THEN
  ASM_SIMP_TAC (srw_ss()) [] )
THEN1 (
  FULL_SIMP_TAC (srw_ss()) [] THEN
  `wfs sx` by METIS_TAC [unify_unifier] THEN
  Q.MATCH_ASSUM_RENAME_TAC `walk s t1 = Pair t1a t1d` [] THEN
  Q.MATCH_ASSUM_RENAME_TAC `walk s t2 = Pair t2a t2d` [] THEN
  (unify_mgu |> Q.SPECL [`s`,`t1a`,`t2a`,`sx`,`s2`] |> MP_TAC) THEN
  SRW_TAC [][] )
THEN1 (
  Cases_on `vwalk s2 n` THEN FULL_SIMP_TAC (srw_ss()) [] ))

val _ = set_fixity "COMPAT" (Infix(NONASSOC,450))
val COMPAT_def = Define`
  s COMPAT s0 = wfs s /\ wfs s0 /\
                (!t.walkstar s (walkstar s0 t) = walkstar s t)`
val _ = TeX_notation {hol = "COMPAT", TeX = ("\\ensuremath{\\Supset}",1)}

val SUBMAP_COMPAT = Q.store_thm(
"SUBMAP_COMPAT",
`wfs sx /\ s SUBMAP sx ==> sx COMPAT s`,
STRIP_TAC THEN
`wfs s` by METIS_TAC [wfs_SUBMAP] THEN
SRW_TAC [][COMPAT_def,walkstar_SUBMAP])

val COMPAT_REFL = Q.store_thm(
"COMPAT_REFL",
`wfs s ==> s COMPAT s`,
SRW_TAC [][COMPAT_def] THEN
METIS_TAC [walkstar_idempotent])

val COMPAT_TRANS = Q.store_thm(
"COMPAT_TRANS",
`s2 COMPAT s1 /\ s1 COMPAT s0 ==> s2 COMPAT s0`,
SRW_TAC [][COMPAT_def] THEN
METIS_TAC [])

val COMPAT_extend = Q.store_thm(
"COMPAT_extend",
`sx COMPAT s /\ wfs (s|+(vx,tx)) /\ vx NOTIN FDOM s /\
 (walkstar sx (Var vx) = walkstar sx tx) ==>
 sx COMPAT (s|+(vx,tx))`,
SRW_TAC [][COMPAT_def] THEN
METIS_TAC [walkstar_extend])

val COMPAT_eqs_unify = Q.store_thm(
"COMPAT_eqs_unify",
`!s t1 t2 sx.sx COMPAT s /\
  (walkstar sx t1 = walkstar sx t2) ==>
  ?si.(unify s t1 t2 = SOME si) /\ sx COMPAT si`,
SRW_TAC [][COMPAT_def] THEN
(eqs_unify |> Q.INST [`s2`|->`sx`] |> MP_TAC) THEN
SRW_TAC [][] THEN
Q.EXISTS_TAC `sx'` THEN
SRW_TAC [][] THEN1
METIS_TAC [unify_unifier] THEN
(unify_mgu |> Q.SPECL [`s`,`t1`,`t2`,`sx'`,`sx`] |> MP_TAC) THEN
SRW_TAC [][])

val COMPAT_more_specific = Q.store_thm(
"COMPAT_more_specific",
`(s COMPAT s0) ⇔
    wfs s ∧ wfs s0 ∧
    (∀t1 t2. (walk* s0 t1 = walk* s0 t2) ⇒ (walk* s t1 = walk* s t2))`,
SRW_TAC [][COMPAT_def,EQ_IMP_THM] THEN1 (
  FIRST_ASSUM (Q.SPEC_THEN `t1` MP_TAC) THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `t2` MP_TAC) THEN
  SRW_TAC [][] ) THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`walk* s0 t`,`t`] MP_TAC) THEN
SRW_TAC [][walkstar_idempotent]);

val _ = export_theory ();
