(* Fixed-points over sets ordered by subset.  Basically, a set-specific
   instantiation of the general theory in posetTheory
*)
Theory fixedPoint[bare]
Ancestors
  poset pred_set
Libs
  HolKernel Parse boolLib BasicProvers simpLib boolSimps
  pred_setLib


Definition monotone_def[nocompute]:
  monotone f = !X Y. X SUBSET Y ==> f X SUBSET f Y
End

val _ = app (ignore o hide) ["lfp", "gfp"]
Overload po_lfp = “poset$lfp”
Overload po_gfp = “poset$gfp”
Definition lfp_def[nocompute]:
  lfp f = BIGINTER { X | f X SUBSET X }
End

Definition gfp_def[nocompute]:
  gfp f = BIGUNION { X | X SUBSET f X }
End

Definition closed_def[nocompute]:
  closed f X <=> f X SUBSET X
End

Definition dense_def[nocompute]:
  dense f X <=> X SUBSET f X
End

Theorem SUBSET_poset[simp]:
  poset (UNIV, $SUBSET)
Proof
  SIMP_TAC (srw_ss()) [poset_def] >>
  PROVE_TAC[SUBSET_ANTISYM, SUBSET_TRANS]
QED

Theorem SUBSET_complete[simp]:
  complete (UNIV, $SUBSET)
Proof
  SIMP_TAC (srw_ss()) [complete_def, lub_def, glb_def] >>
  Q.X_GEN_TAC ‘C’ >> conj_tac
  >- (Q.EXISTS_TAC ‘BIGUNION C’ >> conj_tac
      >- REWRITE_TAC[SIMP_RULE(srw_ss()) [IN_DEF] SUBSET_BIGUNION_I] >>
      SIMP_TAC (srw_ss()) [SUBSET_DEF, IN_DEF] >> PROVE_TAC[]) >>
  Q.EXISTS_TAC ‘BIGINTER C’ >> SIMP_TAC (srw_ss()) [SUBSET_DEF, IN_DEF]
QED

Theorem monotonic_monotone[simp]:
  monotonic (UNIV, $SUBSET) f <=> monotone f
Proof
  SIMP_TAC (srw_ss())[monotone_def, monotonic_def]
QED

Theorem lfp_least_closed:
  !f. monotone f ==> closed f (lfp f) /\ !X. closed f X ==> lfp f SUBSET X
Proof
  rpt strip_tac >> rewrite_tac [lfp_def]
  >- (SIMP_TAC (srw_ss()) [closed_def] >> irule SUBSET_TRANS >>
      Q.EXISTS_TAC ‘BIGINTER { f X | X | f X SUBSET X }’ >>
      CONJ_TAC THENL [
        SIMP_TAC (srw_ss()) [SUBSET_BIGINTER] >> REPEAT STRIP_TAC >>
        FIRST_X_ASSUM SUBST_ALL_TAC >>
        ‘BIGINTER { X | f X SUBSET X } SUBSET X’
          suffices_by PROVE_TAC [monotone_def] >>
        ONCE_REWRITE_TAC [SUBSET_DEF] >> ASM_SIMP_TAC (srw_ss()) [],
        ASM_SIMP_TAC (srw_ss()) [SUBSET_DEF, PULL_EXISTS]
      ]) >>

  ONCE_REWRITE_TAC [SUBSET_DEF] >> FULL_SIMP_TAC (srw_ss()) [closed_def]
QED

Theorem gfp_greatest_dense:
  !f. monotone f ==> dense f (gfp f) /\ !X. dense f X ==> X SUBSET gfp f
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC [gfp_def] THENL [
    SIMP_TAC bool_ss [dense_def] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    Q.EXISTS_TAC ‘BIGUNION { f X | X | X SUBSET f X }’ THEN
    CONJ_TAC THENL [
      CONV_TAC (REWR_CONV SUBSET_DEF) THEN
      SRW_TAC [][] THEN PROVE_TAC [SUBSET_DEF],
      SRW_TAC [][BIGUNION_SUBSET] THEN
      Q_TAC SUFF_TAC ‘X SUBSET BIGUNION {X | X SUBSET f X}’ THEN1
        PROVE_TAC [monotone_def] THEN
      ONCE_REWRITE_TAC [SUBSET_DEF] THEN
      SRW_TAC [][] THEN PROVE_TAC []
    ],

    ONCE_REWRITE_TAC [SUBSET_DEF] THEN
    FULL_SIMP_TAC (srw_ss())[dense_def] THEN PROVE_TAC []
  ]
QED

Theorem lfp_fixedpoint:
  !f. monotone f ==> f (lfp f) = lfp f /\ !X. f X = X ==> lfp f SUBSET X
Proof
  reverse (rpt strip_tac)
  >- (‘f X SUBSET X’ by PROVE_TAC [SUBSET_REFL] THEN
      ‘closed f X’ by PROVE_TAC [closed_def] THEN
      PROVE_TAC [lfp_least_closed]) >>
  ‘f (lfp f) SUBSET lfp f’ by PROVE_TAC [closed_def, lfp_least_closed] THEN
  ‘f (f (lfp f)) SUBSET f (lfp f)’ by PROVE_TAC [monotone_def] THEN
  ‘closed f (f (lfp f))’ by PROVE_TAC [closed_def] THEN
  ‘lfp f SUBSET f (lfp f)’ by PROVE_TAC [lfp_least_closed] THEN
  PROVE_TAC [SUBSET_ANTISYM]
QED

Theorem lfp_poset_lfp:
  monotone f ==> po_lfp (UNIV,$SUBSET) f (lfp f)
Proof
  SIMP_TAC (srw_ss())[posetTheory.lfp_def, lfp_fixedpoint] >>
  PROVE_TAC[lfp_least_closed, closed_def]
QED

Theorem gfp_greatest_fixedpoint:
  !f. monotone f ==> f (gfp f) = gfp f /\ !X. f X = X ==> X SUBSET gfp f
Proof
  rpt strip_tac THENL [
    ‘gfp f SUBSET f (gfp f)’ by PROVE_TAC [dense_def, gfp_greatest_dense] THEN
    ‘f (gfp f) SUBSET f (f (gfp f))’ by PROVE_TAC [monotone_def] THEN
    ‘dense f (f (gfp f))’ by PROVE_TAC [dense_def] THEN
    ‘f (gfp f) SUBSET gfp f’ by PROVE_TAC [gfp_greatest_dense] THEN
    PROVE_TAC [SUBSET_ANTISYM],
    ‘X SUBSET f X’ by PROVE_TAC [SUBSET_REFL] THEN
    ‘dense f X’ by PROVE_TAC [dense_def] THEN
    PROVE_TAC [gfp_greatest_dense]
  ]
QED

Theorem gfp_poset_gfp:
  monotone f ==> po_gfp (UNIV,$SUBSET) f (gfp f)
Proof
  SIMP_TAC (srw_ss()) [posetTheory.gfp_def, gfp_greatest_fixedpoint] >>
  PROVE_TAC[dense_def, gfp_greatest_dense]
QED

Theorem lfp_induction:   !f. monotone f ==> !X. f X SUBSET X ==> lfp f SUBSET X
Proof PROVE_TAC [lfp_least_closed, closed_def]
QED

Theorem gfp_coinduction: !f. monotone f ==> !X. X SUBSET f X ==> X SUBSET gfp f
Proof PROVE_TAC [gfp_greatest_dense, dense_def]
QED

local
  val lemma = prove(“monotone f ==> !X. f (X INTER lfp f) SUBSET lfp f”,
                    PROVE_TAC [INTER_SUBSET, monotone_def, lfp_fixedpoint])
in
Theorem lfp_strong_induction =
  lfp_induction |> SPEC_ALL |> UNDISCH |> Q.SPEC ‘X INTER lfp f’
                |> REWRITE_RULE [SUBSET_INTER, SUBSET_REFL]
                |> ASM_SIMP_RULE bool_ss [lemma] |> Q.GEN ‘X’ |> DISCH_ALL
                |> GEN_ALL;
end

local
  val lemma = prove(“monotone f ==> !X. gfp f SUBSET f (X UNION gfp f)”,
                    PROVE_TAC [SUBSET_UNION, monotone_def,
                               gfp_greatest_fixedpoint])
in
Theorem gfp_strong_coinduction =
           (GEN_ALL o DISCH_ALL o GEN “X:'a -> bool” o
            ASM_SIMP_RULE bool_ss [lemma] o
            REWRITE_RULE [UNION_SUBSET, SUBSET_REFL] o Q.SPEC ‘X UNION gfp f’ o
            UNDISCH o SPEC_ALL) gfp_coinduction;
end;

Definition fnsum_def[nocompute]:
  fnsum f1 f2 X = f1 X UNION f2 X
End

val _ = set_fixity "++" (Infixl 480)
val _ = inferior_overload_on ("++", “fnsum”);

Theorem fnsum_monotone:
   !f1 f2. monotone f1 /\ monotone f2 ==> monotone (fnsum f1 f2)
Proof
  ASM_SIMP_TAC bool_ss [fnsum_def, monotone_def] THEN
  REPEAT STRIP_TAC THEN
  ‘f1 X SUBSET f1 Y’ by PROVE_TAC [] THEN
  ‘f2 X SUBSET f2 Y’ by PROVE_TAC [] THEN
  PROVE_TAC [SUBSET_DEF, IN_UNION]
QED

Definition empty_def[nocompute]: empty = \X. {}
End

Theorem empty_monotone:
   monotone empty
Proof
  SRW_TAC [][monotone_def, empty_def]
QED

Theorem fnsum_empty:
   !f. (f ++ empty = f) /\ (empty ++ f = f)
Proof
  SRW_TAC [][empty_def, fnsum_def, FUN_EQ_THM]
QED

Theorem fnsum_ASSOC:
   !f g h. fnsum f (fnsum g h) = fnsum (fnsum f g) h
Proof
  REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN
  SIMP_TAC bool_ss [fnsum_def, UNION_ASSOC]
QED

Theorem fnsum_COMM:
   !f g. fnsum f g = fnsum g f
Proof
  REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN
  SIMP_TAC bool_ss [fnsum_def, UNION_COMM]
QED


Theorem fnsum_SUBSET:
   !f g X. f X SUBSET fnsum f g X /\ g X SUBSET fnsum f g X
Proof
  SIMP_TAC bool_ss [fnsum_def, SUBSET_DEF, IN_UNION]
QED

Theorem lfp_fnsum:
   !f1 f2. monotone f1 /\ monotone f2 ==>
            lfp f1 SUBSET lfp (fnsum f1 f2) /\
            lfp f2 SUBSET lfp (fnsum f1 f2)
Proof
  PROVE_TAC [lfp_least_closed, closed_def, fnsum_monotone,
             fnsum_SUBSET, SUBSET_TRANS, lfp_induction]
QED

Theorem lfp_rule_applied:
   !f X y. monotone f /\ X SUBSET lfp f /\ y IN f X ==> y IN lfp f
Proof
  REPEAT STRIP_TAC THEN
  ‘f X SUBSET f (lfp f)’ by PROVE_TAC [monotone_def] THEN
  PROVE_TAC [lfp_fixedpoint, SUBSET_DEF]
QED

Theorem lfp_empty:
   !f x. monotone f /\ x IN f {} ==> x IN lfp f
Proof
  PROVE_TAC [EMPTY_SUBSET, lfp_rule_applied]
QED

