open HolKernel boolLib bossLib Parse pred_setTheory relationTheory finite_mapTheory termTheory ramanaLib pairTheory bagTheory prim_recTheory substTheory walkTheory walkstarTheory

val _ = new_theory "redUnif"
val _ = metisTools.limit :=  { time = NONE, infs = SOME 5000 }

val istep_def = Define`
  istep (sl,bl) (sr,br) =
  (∃t. (br + {|(t, t)|} = bl) ∧
       (sr = sl)) ∨
  (∃t1a t1d t2a t2d.
    (br + {|(Pair t1a t1d, Pair t2a t2d)|} = {|(t1a,t2a); (t1d,t2d)|} + bl) ∧
    (sr = sl)) ∨
  (∃v t bi.
    ((bi + {|(Var v, t)|} = bl) ∨
     (bi + {|(t, Var v)|} = bl)) ∧
    v ∉ vars t ∧
    (br = BAG_IMAGE (λ(t1,t2). ((FEMPTY|+(v,t)) '' t1, (FEMPTY|+(v,t)) '' t2)) bi) ∧
    (sr = sl |+ (v,t)))`;

val tstep_def = Define`
  tstep (sl,bl) (sr,br) =
  (∃t1 t2.
    (walk sl t1 = walk sl t2) ∧
    (br + {|(t1,t2)|} = bl) ∧
    (sr = sl)) ∨
  (∃t1 t2 t1a t1d t2a t2d.
    (walk sl t1 = Pair t1a t1d) ∧ (walk sl t2 = Pair t2a t2d) ∧
    (br + {|(t1,t2)|} = {|(t1a,t2a); (t1d,t2d)|} + bl) ∧
    (sr = sl)) ∨
  (∃t1 t2 v t.
    ((walk sl t1 = Var v) ∧ (walk sl t2 = t) ∨
     (walk sl t1 = t) ∧ (walk sl t2 = Var v)) ∧
    ¬ oc sl t v ∧
    (br + {|(t1,t2)|} = bl) ∧
    (sr = sl |+ (v,t)))`;

open unifDefTheory unifPropsTheory;

val wfs_tstep = Q.store_thm(
"wfs_tstep",
`wfs sl ∧ tstep (sl,bl) (sr,br) ⇒ wfs sr`,
SRW_TAC [][tstep_def] THEN SRW_TAC [][] THEN
IMP_RES_TAC walk_to_var THEN
Q.PAT_ASSUM `wfs s` ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [oc_eq_vars_walkstar,walkstar_walk] THEN
MATCH_MP_TAC wfs_extend THEN
METIS_TAC [IN_DEF,walkstar_walk])

val walks_equal = Q.store_thm(
"walks_equal",
`wfs s ∧ (walk s t1 = walk s t2) ⇒ (t1 = t2) ∨ ∃v. (t1 = Var v) ∨ (t2 = Var v)`,
Cases_on `t1 = t2` THEN ASM_SIMP_TAC (srw_ss()) [] THEN
SIMP_TAC (srw_ss()) [GSYM AND_IMP_INTRO] THEN STRIP_TAC THEN
MAP_EVERY Cases_on [`t1`,`t2`] THEN SRW_TAC [][] THEN
METIS_TAC []);

val NOTIN_vars_walk = Q.store_thm(
"NOTIN_vars_walk",
`wfs s ∧ (vwalk s v = walk s t) ∧ (t ≠ Var v) ⇒ v ∉ vars t`,
Cases_on `t` THEN SRW_TAC [][] THEN
SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
`v ∈ vars (vwalk s v)` by SRW_TAC [][] THEN
IMP_RES_TAC vwalk_vR THEN
Q.PAT_ASSUM `vwalk s v = X` ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [wfs_no_cycles] THEN
RES_TAC);

(*
val istep_if_tstep = Q.store_thm(
"istep_if_tstep", (* no! the substitutions won't be equal, they will be equivalent. istep gives an idempotent substitution whereas tstep gives a triangular one! *)
`wfs sl ∧ tstep^* (sl,bl) (sr,br) ⇒ ∃br'. tstep^* (sl,bl) (sr,br')`,
Q_TAC SUFF_TAC
`∀x y. RTC tstep x y ⇒ wfs (FST x) ⇒ ∃br. RTC istep x (FST y,br)`
THEN1 ( SRW_TAC [][] THEN RES_TAC THEN
        FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [] ) THEN
HO_MATCH_MP_TAC RTC_INDUCT THEN
SRW_TAC [][] THEN1 (
  Q.EXISTS_TAC `SND x` THEN SRW_TAC [][] ) THEN
Q.MATCH_ASSUM_RENAME_TAC `tstep a b` [] THEN
MAP_EVERY Cases_on [`a`,`b`] THEN
Q.MATCH_ASSUM_RENAME_TAC `tstep (sl,bl) (si,bi)` [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
IMP_RES_TAC wfs_tstep THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Q.MATCH_ASSUM_RENAME_TAC `istep^* (si,bi) (FST sr,br)` [] THEN

FULL_SIMP_TAC (srw_ss()) [tstep_def] THEN
SRW_TAC [][] THEN1 (
  `(t1 = t2) ∨ (t1 ≠ t2) ∧ ∃v. (t1 = Var v) ∨ (t2 = Var v)`
  by METIS_TAC [walks_equal] THEN
  SRW_TAC [][] THEN1 (
    Q.EXISTS_TAC `br` THEN
    Q.MATCH_ABBREV_TAC `RTC istep pi pr` THEN
    Q_TAC SUFF_TAC `istep pi (si,bi)`
    THEN1 METIS_TAC [RTC_RULES] THEN
    SRW_TAC [][istep_def,Abbr`pi`] ) THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [][] THEN
  TRY (Q.PAT_ASSUM `Var v ≠ t2` (ASSUME_TAC o GSYM)) THEN
  IMP_RES_TAC NOTIN_vars_walk THEN

val tstep_if_istep = Q.store_thm(
"tstep_if_istep", (* need/want idempotent sl instead? *)
`wfs sl ∧ istep^* (sl,bl) (sr,br) ⇒ ∃br'. tstep^* (sl,bl) (sr,br')`,
Q_TAC SUFF_TAC
`∀x y. RTC istep x y ⇒ wfs (FST x) ⇒ ∃br. RTC tstep x (FST y,br)`
THEN1 ( SRW_TAC [][] THEN RES_TAC THEN
        FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [] ) THEN
HO_MATCH_MP_TAC RTC_INDUCT THEN
SRW_TAC [][] THEN1 (
  Q.EXISTS_TAC `SND x` THEN SRW_TAC [][] ) THEN
Q.MATCH_ASSUM_RENAME_TAC `istep a b` [] THEN
MAP_EVERY Cases_on [`a`,`b`] THEN
Q.MATCH_ASSUM_RENAME_TAC `istep (sl,bl) (si,bi)` [] THEN
Q.MATCH_ASSUM_RENAME_TAC `tstep^* (si,bi) (FST sr,br)` [] THEN
FULL_SIMP_TAC (srw_ss()) [istep_def] THEN
SRW_TAC [][] THEN1 (
  Q.EXISTS_TAC `br` THEN
  Q.MATCH_ABBREV_TAC `RTC tstep pi pr` THEN
  Q_TAC SUFF_TAC `tstep pi (si,bi)`
  THEN1 METIS_TAC [RTC_RULES] THEN
  SRW_TAC [][tstep_def,Abbr`pi`] )
THEN1 (
  Q.EXISTS_TAC `br` THEN
  Q.MATCH_ABBREV_TAC `RTC tstep pi pr` THEN
  Q_TAC SUFF_TAC `tstep pi (si,bi)`
  THEN1 METIS_TAC [RTC_RULES] THEN
  SRW_TAC [][tstep_def,Abbr`pi`] THEN
  DISJ2_TAC THEN DISJ1_TAC THEN
  MAP_EVERY Q.EXISTS_TAC [`Pair t1a t1d`,`Pair t2a t2d`,`t1a`,`t1d`,`t2a`,`t2d`] THEN

val tstep_if_unify = Q.store_thm(
"tstep_if_unify",
`wfs s ∧ (unify s t1 t2 = SOME sx) ⇒ tstep^+ (s,b+{|(t1,t2)|}) (sx,b)`,
MAP_EVERY Q.ID_SPEC_TAC [`b`,`sx`,`t2`,`t1`,`s`] THEN
HO_MATCH_MP_TAC unify_ind THEN
SRW_TAC [][] THEN
POP_ASSUM MP_TAC THEN
ASM_SIMP_TAC (srw_ss()) [Once unify_def] THEN
Cases_on `walk s t1` THEN Cases_on `walk s t2` THEN SRW_TAC [][]
THEN1 (MATCH_MP_TAC TC_SUBSET THEN SRW_TAC [][tstep_def])
THEN1 (
  MATCH_MP_TAC TC_SUBSET THEN SRW_TAC [][tstep_def] THEN
  DISJ2_TAC THEN
  MAP_EVERY Q.EXISTS_TAC [`n`,`Var n'`] THEN
  SRW_TAC [][] THEN
  Q.PAT_ASSUM `walk s X = Var n'` MP_TAC THEN
  Cases_on `t2` THEN SRW_TAC [][] THEN
  IMP_RES_TAC vwalk_to_var THEN
  SRW_TAC [][NOT_FDOM_vwalk])
THEN1 (MATCH_MP_TAC TC_SUBSET THEN SRW_TAC [][tstep_def])
THEN1 (MATCH_MP_TAC TC_SUBSET THEN SRW_TAC [][tstep_def])
THEN1 (MATCH_MP_TAC TC_SUBSET THEN SRW_TAC [][tstep_def])
THEN1 (
  Q.PAT_ASSUM `X = SOME sx` ASSUME_TAC THEN
  Q.PAT_ASSUM `wfs s` ASSUME_TAC THEN
  Cases_on `unify s t t'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  `wfs x` by METIS_TAC [unify_uP,uP_def] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `b+{|(t0,t0')|}` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `b` STRIP_ASSUME_TAC) THEN
  Q.PAT_ASSUM `TC tstep X (x,Y)` MP_TAC THEN
  Q.MATCH_ABBREV_TAC `TC tstep p2 (x,Y) ⇒ TC tstep p1 (sx,b)` THEN
  STRIP_TAC THEN Q_TAC SUFF_TAC `tstep p1 p2`
  THEN1 METIS_TAC [TC_RULES] THEN
  SRW_TAC [][tstep_def,Abbr`p2`,Abbr`p1`,Abbr`Y`] THEN
  DISJ2_TAC THEN DISJ1_TAC THEN
  MAP_EVERY Q.EXISTS_TAC [`t1`,`t2`,`t`,`t0`,`t'`,`t0'`] THEN
  SRW_TAC [][ASSOC_BAG_UNION,BAG_INSERT_UNION] THEN
  METIS_TAC [COMM_BAG_UNION,ASSOC_BAG_UNION] )
THEN1 (MATCH_MP_TAC TC_SUBSET THEN SRW_TAC [][tstep_def])
THEN1 (MATCH_MP_TAC TC_SUBSET THEN SRW_TAC [][tstep_def])
);
*)

(*
"unify_if_tstep",
`tstep^+ (s,{|(t1,t2)|}) (sx,{||}) ⇒ ∃su. (unify s t1 t2 = SOME su) ∧ relate sx and su`
*)

(* The above is more like Urban's paper. The below is following "Term rewriting
and all that" by Baader and Nipkow. It's messier because of the explicit orient
step and because the idempotent substitution is supposed to be read off the
solved form of the state when no reductions are possible.
val istep_def = Define`
  istep f el er =
  (∃c. er + {|(Const c, Const c)|} = el) ∨
  (∃t1a t1d t2a t2d.
    er + {|(Pair t1a t1d, Pair t2a t2d)|} = {|(t1a,t2a); (t1d,t2d)|} + el) ∨
  (∃v t.
    (∀u. t ≠ Var u) ∧
    (er + {|(t,Var v)|} = {|(Var v,t)|} + el)) ∨
  (∃v t.
    (Var v, t) <: el ∧
    v ∉ vars t ∧
    ¬ BAG_EVERY el (λ(t1,t2) v ∉ vars t1 ∧ v ∉ vars t2) ∧
    (er = {|(Var v, t)|} + BAG_IMAGE (el - (Var v, t)) (λ(t1,t2). ((FEMPTY|+(v,t)) '' t1, (FEMPTY|+(v,t)) '' t2))))`;

val tstep_def = Define`
  tstep f (sl,el) (sr,er) =
  (∃t1 t2 c.
    (walk sl t1 = Const c) ∧
    (walk sl t2 = Const c) ∧
    (er + {|(t1,t2)|} = el) ∧
    (sr = sl)) ∨
  (∃t1 t2 t1a t1d t2a t2d.
    (walk sl t1 = Pair t1a t1d) ∧
    (walk sl t2 = Pair t2a t2d) ∧
    (er + {|(t1,t2)|} = {|(t1a,t2a); (t1d,t2d)|} + el) ∧
    (sr = sl)) ∨
  (∃t1 t2 v t.
    (walk sl t1 = t) ∧
    (walk sl t2 = Var v) ∧
    (∀u. t ≠ Var u) ∧
    (er + {|(t1,t2)|} = {|(Var v,t)|} + el) ∧
    (sr = sl)) ∨
  (∃t1 t2 v t.
    (walk sl t1 = Var v) ∧
    (walk sl t2 = t) ∧
    ¬ oc sl v t ∧
    (er + {|(t1,t2)|} = el) ∧
    (sr = sl |+ (v,t)))`;
*)

val _ = export_theory ();
