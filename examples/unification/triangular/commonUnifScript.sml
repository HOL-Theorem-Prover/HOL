open HolKernel boolLib bossLib stringTheory arithmeticTheory pred_setTheory finite_mapTheory prim_recTheory
val _ = new_theory "commonUnif";

val _ = Hol_datatype `
  const = Null
        | Bool of bool
        | Num of num
        | String of string`;

val extension_chain = Q.store_thm(
"extension_chain",
`!subst source z.
  (((FINITE (source z)) /\
    (!m n. m < n ==> (subst m) SUBMAP (subst n)) /\
    (!n. DISJOINT (FDOM (subst n)) (source n)) /\
    (!n. z < n ==> (FDOM (subst n) UNION (source n) = FDOM (subst z) UNION (source z))))
    ==> ?x. !n. x < n ==> ((subst n) = (subst x)))`,
SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
Q_TAC SUFF_TAC
`!m. z <= m ==> ?n.m < n /\ CARD(source n) < CARD(source m)`
THEN1
(DISCH_THEN
 (STRIP_ASSUME_TAC o SIMP_RULE (srw_ss()) [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM]) THEN
`?ff.!n.ff (SUC n) < ff n`
    by (Q.EXISTS_TAC `\n.CARD(source(FUNPOW f n z))` THEN
        SRW_TAC [][FUNPOW_SUC] THEN
        Q_TAC SUFF_TAC `z <= FUNPOW f n z` THEN1 METIS_TAC [] THEN
        Induct_on `n` THEN SRW_TAC [][FUNPOW_SUC] THEN
        RES_TAC THEN DECIDE_TAC) THEN
METIS_TAC [WF_LESS,WF_IFF_WELLFOUNDED,wellfounded_def]) THEN
REPEAT STRIP_TAC THEN
`?n.m < n /\ subst m <> subst n` by METIS_TAC [] THEN
Q.EXISTS_TAC `n` THEN
`z < n` by DECIDE_TAC THEN
`(FDOM (subst n) UNION source n = FDOM (subst m) UNION source m) /\
 FINITE (source m) /\ FINITE (source n)`
   by METIS_TAC [LESS_OR_EQ,FINITE_UNION,FDOM_FINITE] THEN
`subst m SUBMAP subst n` by METIS_TAC [] THEN
`FDOM (subst m) PSUBSET FDOM (subst n)` by METIS_TAC [SUBMAP_DEF,SUBSET_DEF,PSUBSET_DEF,EQ_FDOM_SUBMAP] THEN
`(CARD (FDOM (subst n) UNION source n) = CARD (FDOM (subst n)) + CARD (source n)) /\
 (CARD (FDOM (subst m) UNION source m) = CARD (FDOM (subst m)) + CARD (source m)) /\
 (CARD (FDOM (subst m) UNION source m) = CARD (FDOM (subst n) UNION source n))` by
  METIS_TAC [CARD_UNION,ADD_0,DISJOINT_DEF,CARD_EMPTY,FDOM_FINITE] THEN
`CARD (FDOM (subst m)) < CARD (FDOM (subst n))` by METIS_TAC [CARD_PSUBSET,FDOM_FINITE]
THEN DECIDE_TAC)

val _ = export_theory ();
