open HolKernel Parse boolLib BasicProvers

open dividesTheory pred_setTheory
open gcdTheory simpLib metisLib

val ARITH_ss = numSimps.ARITH_ss

val _ = new_theory "gcdset"

val gcdset_def = new_definition(
  "gcdset_def",
  ``gcdset s =
      if (s = {}) \/ (s = {0}) then 0
      else MAX_SET ({ n | n <= MIN_SET (s DELETE 0) } INTER
                    { d | !e. e IN s ==> divides d e })``);

val FINITE_LEQ_MIN_SET = prove(
  ``FINITE { n | n <= MIN_SET (s DELETE 0) }``,
  Q_TAC SUFF_TAC `
    { n | n <= MIN_SET (s DELETE 0) } = count (MIN_SET (s DELETE 0) + 1)
  ` THEN1 SRW_TAC [][] THEN
  SRW_TAC [ARITH_ss][EXTENSION]);

val NON_EMPTY_INTERSECTION = prove(
  ``s <> {} /\ s <> {0} ==>
    { n | n <= MIN_SET (s DELETE 0) } INTER
    { d | !e. e IN s ==> divides d e}  <> {}``,
  STRIP_TAC THEN SIMP_TAC (srw_ss()) [EXTENSION] THEN Q.EXISTS_TAC `1` THEN
  SRW_TAC [][] THEN DEEP_INTRO_TAC MIN_SET_ELIM THEN
  SRW_TAC [ARITH_ss][EXTENSION] THEN
  FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN METIS_TAC []);

val gcdset_divides = store_thm(
  "gcdset_divides",
  ``!e. e IN s ==> divides (gcdset s) e``,
  SRW_TAC[][gcdset_def] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  DEEP_INTRO_TAC MAX_SET_ELIM THEN
  ASM_SIMP_TAC (srw_ss()) [FINITE_INTER, FINITE_LEQ_MIN_SET,
                           NON_EMPTY_INTERSECTION]);

val DECIDE = numLib.ARITH_PROVE
val gcdset_greatest = store_thm(
  "gcdset_greatest",
  ``(!e. e IN s ==> divides g e) ==> divides g (gcdset s)``,
  SRW_TAC [][gcdset_def] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  DEEP_INTRO_TAC MAX_SET_ELIM THEN
  ASM_SIMP_TAC (srw_ss()) [NON_EMPTY_INTERSECTION, FINITE_LEQ_MIN_SET] THEN
  Q.X_GEN_TAC `m` THEN REPEAT STRIP_TAC THEN
  Q.ABBREV_TAC `L = lcm g m` THEN
  `(!e. e IN s ==> divides L e) /\ divides m L /\ divides g L`
    by METIS_TAC [gcdTheory.LCM_IS_LEAST_COMMON_MULTIPLE] THEN
  `?x. x IN s /\ x <> 0`
    by (FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN METIS_TAC []) THEN
  `L <= MIN_SET (s DELETE 0)`
    by (DEEP_INTRO_TAC MIN_SET_ELIM THEN SRW_TAC [][EXTENSION]
          THEN1 METIS_TAC [] THEN
        METIS_TAC [DIVIDES_LE, DECIDE ``x <> 0 <=> 0 < x``]) THEN
  `L <= m` by METIS_TAC[] THEN
  Q_TAC SUFF_TAC `0 < m /\ 0 < g` THEN1
    METIS_TAC [LCM_LE, DECIDE ``x <= y /\ y <= x ==> (x = y)``] THEN
  METIS_TAC [ZERO_DIVIDES, DECIDE ``x <> 0 <=> 0 < x``]);

val gcdset_EMPTY = store_thm(
  "gcdset_EMPTY",
  ``gcdset {} = 0``,
  SRW_TAC [][gcdset_def]);
val _ = export_rewrites ["gcdset_EMPTY"]

val gcdset_INSERT = store_thm(
  "gcdset_INSERT",
  ``gcdset (x INSERT s) = gcd x (gcdset s)``,
  Q.MATCH_ABBREV_TAC `G1 = G2` THEN
  `(!e. e IN s ==> divides G1 e) /\ divides G1 x`
     by METIS_TAC [IN_INSERT, gcdset_divides] THEN
  `divides G2 x /\ divides G2 (gcdset s)`
     by METIS_TAC [GCD_IS_GCD, is_gcd_def] THEN
  MATCH_MP_TAC DIVIDES_ANTISYM THEN CONJ_TAC THENL [
    Q_TAC SUFF_TAC `divides G1 (gcdset s)` THEN1
       METIS_TAC [GCD_IS_GCD, is_gcd_def] THEN
    SRW_TAC [][gcdset_greatest],
    Q_TAC SUFF_TAC `!e. e IN s ==> divides G2 e` THEN1
       METIS_TAC [IN_INSERT, gcdset_greatest] THEN
    METIS_TAC [gcdset_divides, DIVIDES_TRANS]
  ]);
val _ = export_rewrites ["gcdset_INSERT"]


val _ = export_theory()

