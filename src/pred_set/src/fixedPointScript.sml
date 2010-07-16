open HolKernel Parse boolLib

open BasicProvers simpLib boolSimps

val _ = new_theory "fixedPoint";

open pred_setTheory pred_setLib

val monotone_def = new_definition(
  "monotone_def",
  ``monotone f = !X Y. X SUBSET Y ==> f X SUBSET f Y``);

val lfp_def = new_definition(
  "lfp_def",
  ``lfp f = BIGINTER { X | f X SUBSET X }``);

val gfp_def = new_definition(
  "gfp_def",
  ``gfp f = BIGUNION { X | X SUBSET f X }``);

val closed_def = new_definition(
  "closed_def",
  ``closed f X = f X SUBSET X``);

val dense_def = new_definition(
  "dense_def",
  ``dense f X = X SUBSET f X``);

val lfp_least_closed = store_thm(
  "lfp_least_closed",
  ``!f. monotone f ==>
        closed f (lfp f) /\ !X. closed f X ==> lfp f SUBSET X``,
  REPEAT STRIP_TAC THEN REWRITE_TAC [lfp_def] THENL [
    SIMP_TAC (srw_ss()) [closed_def] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    Q.EXISTS_TAC `BIGINTER (GSPEC (\X. (f X, f X SUBSET X)))` THEN
    CONJ_TAC THENL [
      SIMP_TAC (srw_ss()) [SUBSET_BIGINTER] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUFF_TAC ``BIGINTER { X | f X SUBSET X } SUBSET X`` THEN1
        PROVE_TAC [monotone_def] THEN
      ONCE_REWRITE_TAC [SUBSET_DEF] THEN ASM_SIMP_TAC (srw_ss()) [],
      ASM_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN PROVE_TAC []
    ],

    ONCE_REWRITE_TAC [SUBSET_DEF] THEN FULL_SIMP_TAC (srw_ss()) [closed_def]
  ]);

val gfp_greatest_dense = store_thm(
  "gfp_greatest_dense",
  ``!f. monotone f ==>
        dense f (gfp f) /\ !X. dense f X ==> X SUBSET gfp f``,
  REPEAT STRIP_TAC THEN REWRITE_TAC [gfp_def] THENL [
    SIMP_TAC bool_ss [dense_def] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    Q.EXISTS_TAC `BIGUNION (GSPEC (\X. (f X, X SUBSET f X)))` THEN
    CONJ_TAC THENL [
      CONV_TAC (REWR_CONV SUBSET_DEF) THEN
      SRW_TAC [][] THEN PROVE_TAC [SUBSET_DEF],
      SRW_TAC [][BIGUNION_SUBSET] THEN
      Q_TAC SUFF_TAC `X SUBSET BIGUNION {X | X SUBSET f X}` THEN1
        PROVE_TAC [monotone_def] THEN
      ONCE_REWRITE_TAC [SUBSET_DEF] THEN
      SRW_TAC [][] THEN PROVE_TAC []
    ],

    ONCE_REWRITE_TAC [SUBSET_DEF] THEN
    FULL_SIMP_TAC (srw_ss())[dense_def] THEN PROVE_TAC []
  ]);

val lfp_least_fixedpoint = store_thm(
  "lfp_fixedpoint",
  ``!f. monotone f ==> (lfp f = f (lfp f)) /\
                       (!X. (X = f X) ==> lfp f SUBSET X)``,
  REPEAT STRIP_TAC THENL [
    `f (lfp f) SUBSET lfp f` by PROVE_TAC [closed_def, lfp_least_closed] THEN
    `f (f (lfp f)) SUBSET f (lfp f)` by PROVE_TAC [monotone_def] THEN
    `closed f (f (lfp f))` by PROVE_TAC [closed_def] THEN
    `lfp f SUBSET f (lfp f)` by PROVE_TAC [lfp_least_closed] THEN
    PROVE_TAC [SUBSET_ANTISYM],
    `f X SUBSET X` by PROVE_TAC [SUBSET_REFL] THEN
    `closed f X` by PROVE_TAC [closed_def] THEN
    PROVE_TAC [lfp_least_closed]
  ]);

val gfp_greatest_fixedpoint = store_thm(
  "gfp_greatest_fixedpoint",
  ``!f. monotone f ==> (gfp f = f (gfp f)) /\
                       (!X. (X = f X) ==> X SUBSET gfp f)``,
  REPEAT STRIP_TAC THENL [
    `gfp f SUBSET f (gfp f)` by PROVE_TAC [dense_def, gfp_greatest_dense] THEN
    `f (gfp f) SUBSET f (f (gfp f))` by PROVE_TAC [monotone_def] THEN
    `dense f (f (gfp f))` by PROVE_TAC [dense_def] THEN
    `f (gfp f) SUBSET gfp f` by PROVE_TAC [gfp_greatest_dense] THEN
    PROVE_TAC [SUBSET_ANTISYM],
    `X SUBSET f X` by PROVE_TAC [SUBSET_REFL] THEN
    `dense f X` by PROVE_TAC [dense_def] THEN
    PROVE_TAC [gfp_greatest_dense]
  ]);

val lfp_induction = store_thm(
  "lfp_induction",
  ``!f. monotone f ==> !X. f X SUBSET X ==> lfp f SUBSET X``,
  PROVE_TAC [lfp_least_closed, closed_def]);

val gfp_coinduction = store_thm(
  "gfp_coinduction",
  ``!f. monotone f ==> !X. X SUBSET f X ==> X SUBSET gfp f``,
  PROVE_TAC [gfp_greatest_dense, dense_def]);

val lfp_strong_induction = let
  val lemma = prove(``monotone f ==> !X. f (X INTER lfp f) SUBSET lfp f``,
                    PROVE_TAC [INTER_SUBSET, monotone_def,
                               lfp_least_fixedpoint])
in
  save_thm("lfp_strong_induction",
           (GEN_ALL o DISCH_ALL o GEN ``X:'a -> bool`` o
            ASM_SIMP_RULE bool_ss [lemma] o
            REWRITE_RULE [SUBSET_INTER, SUBSET_REFL] o Q.SPEC `X INTER lfp f` o
            UNDISCH o SPEC_ALL) lfp_induction)
end;

val gfp_strong_coinduction = let
  val lemma = prove(``monotone f ==> !X. gfp f SUBSET f (X UNION gfp f)``,
                    PROVE_TAC [SUBSET_UNION, monotone_def,
                               gfp_greatest_fixedpoint])
in
  save_thm("gfp_strong_coinduction",
           (GEN_ALL o DISCH_ALL o GEN ``X:'a -> bool`` o
            ASM_SIMP_RULE bool_ss [lemma] o
            REWRITE_RULE [UNION_SUBSET, SUBSET_REFL] o Q.SPEC `X UNION gfp f` o
            UNDISCH o SPEC_ALL) gfp_coinduction)
end;

val fnsum_def = new_definition(
  "fnsum_def",
  ``fnsum f1 f2 X = f1 X UNION f2 X``);

val _ = set_fixity "++" (Infixl 480)
val _ = overload_on ("++", ``fnsum``);

val fnsum_monotone = store_thm(
  "fnsum_monotone",
  ``!f1 f2. monotone f1 /\ monotone f2 ==> monotone (fnsum f1 f2)``,
  ASM_SIMP_TAC bool_ss [fnsum_def, monotone_def] THEN
  REPEAT STRIP_TAC THEN
  `f1 X SUBSET f1 Y` by PROVE_TAC [] THEN
  `f2 X SUBSET f2 Y` by PROVE_TAC [] THEN
  PROVE_TAC [SUBSET_DEF, IN_UNION]);

val empty_def = new_definition("empty_def", ``empty = \X. {}``);

val empty_monotone = store_thm(
  "empty_monotone",
  ``monotone empty``,
  SRW_TAC [][monotone_def, empty_def]);

val fnsum_empty = store_thm(
  "fnsum_empty",
  ``!f. (f ++ empty = f) /\ (empty ++ f = f)``,
  SRW_TAC [][empty_def, fnsum_def, FUN_EQ_THM]);

val fnsum_ASSOC = store_thm(
  "fnsum_ASSOC",
  ``!f g h. fnsum f (fnsum g h) = fnsum (fnsum f g) h``,
  REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN
  SIMP_TAC bool_ss [fnsum_def, UNION_ASSOC]);

val fnsum_COMM = store_thm(
  "fnsum_COMM",
  ``!f g. fnsum f g = fnsum g f``,
  REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN
  SIMP_TAC bool_ss [fnsum_def, UNION_COMM]);


val fnsum_SUBSET = store_thm(
  "fnsum_SUBSET",
  ``!f g X. f X SUBSET fnsum f g X /\ g X SUBSET fnsum f g X``,
  SIMP_TAC bool_ss [fnsum_def, SUBSET_DEF, IN_UNION]);

val lfp_fnsum = store_thm(
  "lfp_fnsum",
  ``!f1 f2. monotone f1 /\ monotone f2 ==>
            lfp f1 SUBSET lfp (fnsum f1 f2) /\
            lfp f2 SUBSET lfp (fnsum f1 f2)``,
  PROVE_TAC [lfp_least_closed, closed_def, fnsum_monotone,
             fnsum_SUBSET, SUBSET_TRANS, lfp_induction]);

val lfp_rule_applied = store_thm(
  "lfp_rule_applied",
  ``!f X y. monotone f /\ X SUBSET lfp f /\ y IN f X ==> y IN lfp f``,
  REPEAT STRIP_TAC THEN
  `f X SUBSET f (lfp f)` by PROVE_TAC [monotone_def] THEN
  PROVE_TAC [lfp_least_fixedpoint, SUBSET_DEF]);

val lfp_empty = store_thm(
  "lfp_empty",
  ``!f x. monotone f /\ x IN f {} ==> x IN lfp f``,
  PROVE_TAC [EMPTY_SUBSET, lfp_rule_applied]);

val _ = export_theory();
