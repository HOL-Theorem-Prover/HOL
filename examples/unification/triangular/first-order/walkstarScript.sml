open HolKernel Parse boolLib bossLib ramanaLib relationTheory pairTheory
     bagTheory prim_recTheory finite_mapTheory substTheory termTheory walkTheory

val _ = new_theory "walkstar"

val pre_walkstar_def = TotalDefn.xDefineSchema "pre_walkstar"
 `walkstar t =
    case walk s t
    of Pair t1 t2 => Pair (walkstar t1) (walkstar t2)
     | w => w`;

val _ = overload_on("walk*",``walkstar``)

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "◁", BreakSpace(1,0)],
                  term_name = "walk*",
                  fixity = Infixr 700}

Definition walkstarR_def:
  walkstarR s =
   inv_image ((LEX) (mlt1 (vR s)^+)^+ (measure pair_count)) (\t. (varb t, t))
End

val [h2,h1,hWF] = hyp pre_walkstar_def;
val _ = store_term_thm ("walkstar_hWF", hWF);
val _ = store_term_thm ("walkstar_h1", h1);
val _ = store_term_thm ("walkstar_h2", h2);
val _ = store_term_thm ("walkstar_def_print",
TermWithCase`
wfs s ⇒
(walk* s t =
  case walk s t
  of Pair t1 t2 => Pair (walk* s t1) (walk* s t2)
   | t' => t')`)

val inst_walkstar =  Q.INST [`R` |-> `walkstarR s`]

val [h2,h1,h3] = hyp (inst_walkstar pre_walkstar_def)

val walkstar_th1 = Q.store_thm("walkstar_th1",`wfs s ⇒ ^h1`,
SRW_TAC [][inv_image_def,LEX_DEF,walkstarR_def] >>
Q.PAT_X_ASSUM `wfs s` ASSUME_TAC >>
Cases_on `t` >> FULL_SIMP_TAC (srw_ss()) [] >| [
  MATCH_MP_TAC TC_SUBSET >>
  SRW_TAC [][mlt1_def] >>
  MAP_EVERY Q.EXISTS_TAC [`n`,`varb t1`,`{||}`] >>
  SRW_TAC [][vwalk_vR],
  REPEAT (Q.PAT_X_ASSUM `X = Y` (K ALL_TAC)) >>
  Cases_on `varb t2 = {||}` THEN1
    SRW_TAC [ARITH_ss][measure_thm] >>
  DISJ1_TAC >> MATCH_MP_TAC TC_mlt1_UNION2_I >>
  SRW_TAC [][]
]);

val walkstar_th2 = Q.store_thm("walkstar_th2",`wfs s ⇒ ^h2`,
SRW_TAC [][inv_image_def,LEX_DEF,walkstarR_def] >>
Q.PAT_X_ASSUM `wfs s` ASSUME_TAC >>
Cases_on `t` >> FULL_SIMP_TAC (srw_ss()) [] >| [
  MATCH_MP_TAC TC_SUBSET >>
  SRW_TAC [][mlt1_def] >>
  MAP_EVERY Q.EXISTS_TAC [`n`,`varb t2`,`{||}`] >>
  SRW_TAC [][vwalk_vR],
  REPEAT (Q.PAT_X_ASSUM `X = Y` (K ALL_TAC)) >>
  Cases_on `varb t1 = {||}` THEN1
    SRW_TAC [ARITH_ss][measure_thm] >>
  DISJ1_TAC >>
  Q.MATCH_ABBREV_TAC `(mlt1 R)^+ b2 (b1 + b2)` >>
  Q_TAC SUFF_TAC `(mlt1 R)^+ b2 (b2 + b1)` THEN1
    METIS_TAC [COMM_BAG_UNION] >>
  MATCH_MP_TAC TC_mlt1_UNION2_I >>
  UNABBREV_ALL_TAC >>
  SRW_TAC [][]
]);

val walkstar_thWF = Q.store_thm("walkstar_thWF",`wfs s ⇒ ^h3`,
SRW_TAC [][wfs_def,walkstarR_def] >>
MATCH_MP_TAC WF_inv_image >>
SRW_TAC [][WF_TC, WF_LEX, WF_mlt1]);

fun walkstar_wfs_hyp th =
  th |>
  PROVE_HYP (UNDISCH walkstar_th1) |>
  PROVE_HYP (UNDISCH walkstar_th2) |>
  PROVE_HYP (UNDISCH walkstar_thWF);

Theorem walkstar_def =
  DISCH_ALL(walkstar_wfs_hyp (inst_walkstar pre_walkstar_def))
Theorem walkstar_ind =
  walkstar_wfs_hyp (inst_walkstar (theorem "pre_walkstar_ind"))

val walkstar_thm = RWsave_thm(
  "walkstar_thm",
[walkstar_def |> UNDISCH |> Q.SPEC `Var v` |> SIMP_RULE (srw_ss()) [],
 walkstar_def |> UNDISCH |> Q.SPEC `Pair t1 t2` |> SIMP_RULE (srw_ss()) [],
 walkstar_def |> UNDISCH |> Q.SPEC `Const c` |> SIMP_RULE (srw_ss()) []]
|> LIST_CONJ |> DISCH_ALL);

val walkstar_FEMPTY = RWstore_thm(
"walkstar_FEMPTY",
`!t.(walk* FEMPTY t = t)`,
ASSUME_TAC wfs_FEMPTY >>
HO_MATCH_MP_TAC (Q.INST[`s`|->`FEMPTY`]walkstar_ind) >>
Cases_on `t` >> SRW_TAC [][]);

val NOT_FDOM_walkstar = Q.store_thm(
"NOT_FDOM_walkstar",
`wfs s ==> !t. v NOTIN FDOM s ==> v IN vars t ==> v IN vars (walk* s t)`,
DISCH_TAC >> HO_MATCH_MP_TAC walkstar_ind >> SRW_TAC [][] >> Cases_on `t` >| [
  Q.PAT_X_ASSUM `wfs s` ASSUME_TAC >>
  FULL_SIMP_TAC (srw_ss()) [Once vwalk_def, vars_def, FLOOKUP_DEF],
  Q.PAT_X_ASSUM `wfs s` ASSUME_TAC >> FULL_SIMP_TAC (srw_ss()) [],
  FULL_SIMP_TAC (srw_ss()) [vars_def]]);

val vwalk_EQ_var_vR = prove(
  ``wfs s ==> !u v1 v2. (vwalk s u = Var v1) /\ (vR s)^+ v2 u /\
                        v2 NOTIN FDOM s ==> (v1 = v2)``,
  STRIP_TAC >> HO_MATCH_MP_TAC vwalk_ind >> SRW_TAC [][] >>
  IMP_RES_TAC TC_CASES2 >>
  FULL_SIMP_TAC (srw_ss()) [vR_def] >>
  Cases_on `FLOOKUP s u` >> FULL_SIMP_TAC (srw_ss()) [] >>
  Q.PAT_X_ASSUM `vwalk s u = UU` MP_TAC >>
  SRW_TAC [][Once vwalk_def] >>
  Cases_on `x` >> FULL_SIMP_TAC (srw_ss()) [] >>
  POP_ASSUM MP_TAC >> SRW_TAC [][NOT_FDOM_vwalk]);

val vwalk_EQ_const_vR = prove(
  ``!v u. (vR s)^+ v u ==> v NOTIN FDOM s /\ wfs s ==>
          !c. vwalk s u <> Const c``,
  HO_MATCH_MP_TAC TC_INDUCT_RIGHT1 >> SRW_TAC [][] >| [
    FULL_SIMP_TAC (srw_ss()) [vR_def] >>
    Cases_on `FLOOKUP s u` >> FULL_SIMP_TAC (srw_ss()) [] >>
    SRW_TAC [][Once vwalk_def] >> Cases_on `x` >>
    FULL_SIMP_TAC (srw_ss()) [] >> SRW_TAC [][NOT_FDOM_vwalk],
    FULL_SIMP_TAC (srw_ss()) [vR_def] >>
    Cases_on `FLOOKUP s u'` >> FULL_SIMP_TAC (srw_ss()) [] >>
    SRW_TAC [][Once vwalk_def] >> Cases_on `x` >>
    FULL_SIMP_TAC (srw_ss()) [] >> SRW_TAC [][NOT_FDOM_vwalk]
  ]);

val vwalk_EQ_pair_vR = prove(
  ``!v u. (vR s)^+ v u ==>
          !t1 t2. v NOTIN FDOM s /\ wfs s /\ (vwalk s u = Pair t1 t2) ==>
                  ?u. (u IN vars t1 \/ u IN vars t2) /\ (vR s)^* v u``,
  HO_MATCH_MP_TAC TC_STRONG_INDUCT_RIGHT1 >> SRW_TAC [][] >>
  FULL_SIMP_TAC (srw_ss()) [vR_def] >| [
    Cases_on `FLOOKUP s u` >> FULL_SIMP_TAC (srw_ss()) [] >>
    Q.PAT_X_ASSUM `vwalk s u = XXX` MP_TAC >>
    SRW_TAC [][Once vwalk_def] >>
    Cases_on `x` >> FULL_SIMP_TAC (srw_ss()) [] >| [
      POP_ASSUM MP_TAC >> SRW_TAC [][NOT_FDOM_vwalk],
      Q.EXISTS_TAC `v` >> SRW_TAC [][],
      Q.EXISTS_TAC `v` >> SRW_TAC [][]
    ],
    Cases_on `FLOOKUP s u'` >> FULL_SIMP_TAC (srw_ss()) [] >>
    Q.PAT_X_ASSUM `vwalk s u' = XXX` MP_TAC >>
    SRW_TAC [][Once vwalk_def] >>
    Cases_on `x` >> FULL_SIMP_TAC (srw_ss()) [] >> METIS_TAC [TC_RTC]
  ]);

val TC_vR_vars_walkstar = store_thm(
  "TC_vR_vars_walkstar",
  ``wfs s /\ u IN vars t /\ (vR s)^+ v u /\ v NOTIN FDOM s ==>
    v IN vars (walk* s t)``,
  Q_TAC SUFF_TAC
     `wfs s ==>
     !t v u. (vR s)^+ v u /\ v NOTIN FDOM s /\ u IN vars t ==>
             v IN vars (walk* s t)`
     THEN1 METIS_TAC [] >>
  STRIP_TAC >> HO_MATCH_MP_TAC walkstar_ind >>
  SRW_TAC [][] >> Cases_on `t` >| [
    Q.MATCH_ABBREV_TAC `v IN vars (walk* s (Var s'))` >>
    FULL_SIMP_TAC (srw_ss()) [] >> SRW_TAC [][] >>
    Cases_on `vwalk s s'` >> SRW_TAC [][] >| [
      METIS_TAC [vwalk_EQ_var_vR],
      `?u. u IN vars (Pair t t0) /\ (vR s)^* v u`
         by (SRW_TAC [][] >> METIS_TAC [vwalk_EQ_pair_vR]) >>
      `(u = v) \/ (vR s)^+ v u`
         by METIS_TAC [EXTEND_RTC_TC_EQN, RTC_CASES1] THEN1
         FULL_SIMP_TAC (srw_ss()) [NOT_FDOM_walkstar] >>
      FULL_SIMP_TAC (srw_ss()) [] >> METIS_TAC [],
      METIS_TAC [vwalk_EQ_const_vR]
    ],
    FULL_SIMP_TAC (srw_ss()) [] >> METIS_TAC [],
    FULL_SIMP_TAC (srw_ss()) []
  ]);

val walkstar_SUBMAP = Q.store_thm(
"walkstar_SUBMAP",
`s SUBMAP sx ∧ wfs sx ⇒ (walk* sx t = walk* sx (walk* s t))`,
STRIP_TAC >> IMP_RES_TAC wfs_SUBMAP >>
Q.ID_SPEC_TAC `t` >>
HO_MATCH_MP_TAC walkstar_ind >>
SRW_TAC [][] >>
Q.PAT_X_ASSUM `wfs s` ASSUME_TAC >>
FULL_SIMP_TAC (srw_ss()) [] >>
Cases_on `t` >> SRW_TAC [][] >>
Q.SPECL_THEN [`n`,`s`] MP_TAC (UNDISCH vwalk_SUBMAP) >>
Cases_on `vwalk s n` >> SRW_TAC [][])

val walkstar_idempotent = Q.store_thm(
"walkstar_idempotent",
`wfs s ==> !t.(walk* s t = walk* s (walk* s t))`,
METIS_TAC [walkstar_SUBMAP,SUBMAP_REFL])

val walkstar_subterm_idem = Q.store_thm(
"walkstar_subterm_idem",
`(walk* s t1 = Pair t1a t1d) ∧ wfs s ⇒
 (walk* s t1a = t1a) ∧
 (walk* s t1d = t1d)`,
SRW_TAC [][] >>
IMP_RES_TAC walkstar_idempotent >>
POP_ASSUM (Q.SPEC_THEN `t1` MP_TAC) >>
FULL_SIMP_TAC (srw_ss()) [])

val walkstar_walk = Q.store_thm(
"walkstar_walk",
`wfs s ==> (walk* s (walk s t) = walk* s t)`,
Cases_on `t` >> SRW_TAC [][] >> SRW_TAC [][] >>
Cases_on `vwalk s n` >> SRW_TAC [][] >>
`vwalk s n' = Var n'` by METIS_TAC [vwalk_to_var,NOT_FDOM_vwalk] >>
SRW_TAC [][])

val walkstar_to_var = Q.store_thm(
"walkstar_to_var",
`(walk* s t = (Var v)) ∧ wfs s ⇒ v NOTIN (FDOM s) ∧ ∃u.t = Var u`,
REVERSE (SRW_TAC [][]) THEN1
(Cases_on `t` >> FULL_SIMP_TAC (srw_ss()) []) >>
IMP_RES_TAC walkstar_idempotent >>
POP_ASSUM (Q.SPEC_THEN `t` MP_TAC) >>
ASM_SIMP_TAC (srw_ss()) [] >>
Cases_on `vwalk s v` >> SRW_TAC [][] >>
METIS_TAC [vwalk_to_var])

open pred_setTheory;

(* direct version of walkstar that does the walk itself *)

val apply_ts_thm = Q.store_thm(
"apply_ts_thm",
`wfs s ⇒
  (walk* s (Var v) =
     case FLOOKUP s v of NONE => (Var v)
                       | SOME t => walk* s t) ∧
  (walk* s (Pair t1 t2) = Pair (walk* s t1) (walk* s t2)) ∧
  (walk* s (Const c) = Const c)`,
SIMP_TAC (srw_ss()) [] >> STRIP_TAC >>
Q.ID_SPEC_TAC `v` >>
HO_MATCH_MP_TAC vwalk_ind >>
SRW_TAC [][] >>
Cases_on `FLOOKUP s v` >> SRW_TAC [][Once vwalk_def] >>
Cases_on `x` >> SRW_TAC [][]);

val apply_ts_ind = save_thm(
"apply_ts_ind",
UNDISCH (Q.prove(
`wfs s ⇒
 ∀P. (∀v. (∀t. (FLOOKUP s v = SOME t) ⇒ P t) ⇒ P (Var v)) ∧
     (∀t1 t2. P t1 ∧ P t2 ⇒ P (Pair t1 t2)) ∧ (∀c. P (Const c)) ⇒
     ∀v. P v`,
SRW_TAC [][] >>
Q.ID_SPEC_TAC `v` >>
HO_MATCH_MP_TAC walkstar_ind >>
STRIP_TAC >> Cases_on `t` >>
SRW_TAC [][] >>
NTAC 2 (POP_ASSUM MP_TAC) >>
Q.ID_SPEC_TAC `n` >>
HO_MATCH_MP_TAC vwalk_ind >>
SRW_TAC [][] >>
Cases_on `FLOOKUP s n` >> FULL_SIMP_TAC (srw_ss()) [] >>
Q.PAT_X_ASSUM `wfs s` ASSUME_TAC >>
FULL_SIMP_TAC (srw_ss()) [Once vwalk_def] >>
Cases_on `x` >> FULL_SIMP_TAC (srw_ss()) [] >>
Q_TAC SUFF_TAC `∀t. (FLOOKUP s n = SOME t) ⇒ P t` THEN1 METIS_TAC [] >>
SRW_TAC [][] >>
Q.PAT_X_ASSUM `∀t1 t2. X ⇒ P t2` MP_TAC >>
SRW_TAC [][Once vwalk_def])));

Theorem vars_walkstar:
  wfs s ⇒
  ∀t. vars (walkstar s t) ⊆ vars t ∪ BIGUNION (FRANGE (vars o_f s))
Proof
STRIP_TAC >> HO_MATCH_MP_TAC apply_ts_ind >>
SRW_TAC [][apply_ts_thm] >| [
  Cases_on `FLOOKUP s t` >> SRW_TAC [][] >>
  `vars x SUBSET BIGUNION (FRANGE (vars o_f s))`
  by (MATCH_MP_TAC SUBSET_BIGUNION_I >>
      MATCH_MP_TAC o_f_FRANGE >>
      METIS_TAC [FRANGE_FLOOKUP]) >>
  MATCH_MP_TAC SUBSET_TRANS >>
  Q.EXISTS_TAC `vars x UNION BIGUNION (FRANGE (vars o_f s))` >> SRW_TAC [][] >>
  MATCH_MP_TAC SUBSET_TRANS >>
  Q.EXISTS_TAC `BIGUNION (FRANGE (vars o_f s))` >> SRW_TAC [][],
  MATCH_MP_TAC SUBSET_TRANS >>
  Q.EXISTS_TAC `vars t UNION BIGUNION (FRANGE (vars o_f s))` >>
  SRW_TAC [][] >>
  METIS_TAC [SUBSET_UNION,UNION_ASSOC],
  MATCH_MP_TAC SUBSET_TRANS >>
  Q.EXISTS_TAC `vars t' UNION BIGUNION (FRANGE (vars o_f s))` >>
  SRW_TAC [][] >>
  METIS_TAC [SUBSET_UNION,UNION_ASSOC,UNION_COMM]
]
QED

(* occurs check, which is (proved) equivalent to vars o walkstar *)

val (oc_rules, oc_ind, oc_cases) = Hol_reln`
  (!t v. v IN vars t /\ v NOTIN FDOM s ==> oc s t v) /\
  (!t v u t'. u IN vars t /\ (vwalk s u = t') /\ oc s t' v ==>
                oc s t v)`;

val oc_strong_ind =
  save_thm("oc_strong_ind",IndDefLib.derive_strong_induction(oc_rules, oc_ind));

val oc_pair_E0 = prove(
  ``!t v. oc s t v ==>
          !t1 t2. (t = Pair t1 t2) ==> oc s t1 v \/ oc s t2 v``,
  HO_MATCH_MP_TAC oc_strong_ind >> CONJ_TAC >| [
    METIS_TAC [IN_UNION, vars_def, oc_rules],
    ALL_TAC
  ] >>
  SRW_TAC [][] >> FULL_SIMP_TAC (srw_ss()) [] >>
  METIS_TAC [oc_rules]);

val oc_pair_E = SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [] oc_pair_E0;

val oc_pair_I = Q.prove(
  `(!t1. oc s t1 v ==> oc s (Pair t1 t2) v) /\
   (!t2. oc s t2 v ==> oc s (Pair t1 t2) v)`,
  REPEAT STRIP_TAC >>
  POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [oc_cases]) >>
  SRW_TAC [][] >>
  METIS_TAC [vars_def, IN_UNION, oc_rules]);

val oc_pair = Q.prove(
  `oc s (Pair t1 t2) v <=> oc s t1 v \/ oc s t2 v`,
  METIS_TAC [oc_pair_E, oc_pair_I]);

val oc_const = Q.prove(
  `~oc s (Const c) v`,
  ONCE_REWRITE_TAC [oc_cases] >> SRW_TAC [][]);

val oc_var1 = Q.prove(
  `!t v. oc s t v ==>
        !u. (t = Var u) /\ wfs s ==>
               case vwalk s u of
                 Var u => (v = u)
               | Pair t1 t2 => oc s t1 v \/ oc s t2 v
               | _ => F`,
  HO_MATCH_MP_TAC oc_strong_ind >> SRW_TAC [][]
    >- (FULL_SIMP_TAC (srw_ss())[] >> SRW_TAC [][Once vwalk_def,FLOOKUP_DEF]) >>
  FULL_SIMP_TAC (srw_ss()) [] >> SRW_TAC [][] >>
  Cases_on `vwalk s u` >> FULL_SIMP_TAC (srw_ss()) [oc_pair,oc_const] >>
  Q.MATCH_ABBREV_TAC `v = n` >>
  `vwalk s n = Var n` by METIS_TAC [vwalk_to_var,NOT_FDOM_vwalk] >>
  FULL_SIMP_TAC (srw_ss()) []);

val oc2 = CONJUNCT2 (SIMP_RULE bool_ss [FORALL_AND_THM] oc_rules);

val oc_var2 = Q.prove(
  `wfs s ==> !v u.
            (case vwalk s v of
                Var u => (x = u)
              | Pair t1 t2 => oc s t1 x \/ oc s t2 x
              | _ => F) ==> oc s (Var v) x`,
  DISCH_TAC >> HO_MATCH_MP_TAC vwalk_ind >> SRW_TAC [][] >>
  Cases_on `vwalk s v` >>
  FULL_SIMP_TAC (srw_ss()) [] >| [
    MATCH_MP_TAC oc2 >> SRW_TAC [][] >>
    Q.MATCH_ABBREV_TAC `oc s (Var n) n` >>
    `n NOTIN FDOM s` by METIS_TAC [vwalk_to_var,NOT_FDOM_vwalk] >>
    METIS_TAC [oc_rules, vars_def, IN_INSERT],
    MATCH_MP_TAC oc2 >> SRW_TAC [][oc_pair],
    MATCH_MP_TAC oc2 >> SRW_TAC [][oc_pair]]);

val oc_var = Q.prove(
  `wfs s ==> (oc s (Var v) x =
                 case vwalk s v of
                    Var u => (x = u)
                  | Pair t1 t2 => oc s t1 x \/ oc s t2 x
                  | _ => F)`,
  METIS_TAC [oc_var2, oc_var1]);

val oc_thm = RWsave_thm("oc_thm", LIST_CONJ [oc_var, oc_pair, oc_const]);

val oc_def_q =
`wfs s ⇒
 (oc s t v =
  case walk s t of
     Var u => (v = u)
   | Pair t1 t2 => oc s t1 v ∨ oc s t2 v
   | _ => F)`;

val oc_walking = Q.store_thm(
"oc_walking", oc_def_q,
Induct_on `t` >> SRW_TAC [][])

val _ = store_term_thm("oc_def_print",TermWithCase oc_def_q);

val oc_if_vars_walkstar = Q.prove(
`wfs s ==> !t. vars (walk* s t) v ==> oc s t v`,
DISCH_TAC >> HO_MATCH_MP_TAC walkstar_ind >> SRW_TAC [] [] >>
Cases_on `t` >| [
  Cases_on `walk* s (Var n)` >> Q.PAT_X_ASSUM `wfs s` ASSUME_TAC
  >| [
    `v = n'` by METIS_TAC [vars_def,IN_DEF,IN_INSERT,NOT_IN_EMPTY] >>
    Cases_on `vwalk s n` >> FULL_SIMP_TAC (srw_ss()) [],
    Cases_on `vwalk s n` >> FULL_SIMP_TAC (srw_ss()) [] >>
    METIS_TAC [IN_UNION,IN_DEF],
    FULL_SIMP_TAC (srw_ss()) [] >> `v IN {}` by METIS_TAC [IN_DEF]
    >> FULL_SIMP_TAC (srw_ss()) [NOT_IN_EMPTY]
  ],
  Q.PAT_X_ASSUM `vars (walkstar s t) v` MP_TAC >> SRW_TAC [][] >>
  Q.PAT_X_ASSUM `wfs s` ASSUME_TAC >> FULL_SIMP_TAC (srw_ss()) [] >>
  METIS_TAC [IN_DEF,IN_UNION],
  Q.PAT_X_ASSUM `wfs s` ASSUME_TAC >>
  FULL_SIMP_TAC (srw_ss()) [] >>
  METIS_TAC [IN_DEF,NOT_IN_EMPTY]]);

val oc_NOTIN_FDOM = Q.store_thm(
  "oc_NOTIN_FDOM",
  `wfs s ==> !t v. oc s t v ==> v NOTIN FDOM s`,
  STRIP_TAC >> HO_MATCH_MP_TAC oc_ind >> SRW_TAC [] []);

val vars_walkstar_if_oc = Q.prove(
`wfs s ==> !t v. oc s t v ==> v IN vars (walkstar s t)`,
STRIP_TAC >> HO_MATCH_MP_TAC oc_strong_ind >> SRW_TAC [] [] >-
  METIS_TAC [NOT_FDOM_walkstar] >>
Induct_on `t` >> SRW_TAC [][] >| [
    Cases_on `vwalk s n` >> SRW_TAC [][] >>
    Q.PAT_X_ASSUM `Y IN vars X` MP_TAC >>
    ASM_SIMP_TAC (srw_ss()) [] >>
   `vwalk s n' = Var n'` by METIS_TAC [vwalk_to_var,NOT_FDOM_vwalk] >>
    SRW_TAC [][],
    METIS_TAC [],
    METIS_TAC []
]);

val oc_eq_vars_walkstar = Q.store_thm(
  "oc_eq_vars_walkstar",
  `wfs s ==> (oc s t v ⇔ v ∈ vars (walkstar s t))`,
  SRW_TAC [][FUN_EQ_THM] >>
  METIS_TAC [vars_walkstar_if_oc,oc_if_vars_walkstar,IN_DEF]);

val _ = export_theory ();
