open HolKernel boolLib Parse bossLib BasicProvers

open wordsTheory integerTheory intLib arithmeticTheory

(* theory of 2's complement representation of integers *)

val _ = new_theory "integer_word"

val i2w_def = Define`
  i2w (i : int) = if i < 0 then word_2comp (n2w (Num ~i)) else n2w (Num i)
`;

val w2i_def = Define`
  w2i w = if word_msb w then ~(int_of_num (w2n (word_2comp w)))
          else int_of_num (w2n w)
`;

val UINT_MAX_def = Define`
  UINT_MAX (x: 'a set) = 2n ** dimindex (UNIV : 'a set) - 1
`;

val INT_MAX_def = Define`
  INT_MAX (x: 'a set) = 2i ** (dimindex (UNIV: 'a set) - 1) - 1
`;
val INT_MIN_def = Define`
  INT_MIN x = ~INT_MAX x - 1
`

val INT_MAX_32 = store_thm(
  "INT_MAX_32",
  ``INT_MAX (s: i32 set) = 2147483647``,
  SRW_TAC [][INT_MAX_def, dimindex_32]);
val _ = export_rewrites ["INT_MAX_32"]

val INT_MIN_32 = store_thm(
  "INT_MIN_32",
  ``INT_MIN (s: i32 set) = ~2147483648``,
  SRW_TAC [][INT_MIN_def]);
val _ = export_rewrites ["INT_MIN_32"]

val UINT_MAX_32 = store_thm(
  "UINT_MAX_32",
  ``UINT_MAX (s: i32 set) = 4294967295``,
  SRW_TAC [][UINT_MAX_def, dimindex_32]);
val _ = export_rewrites ["UINT_MAX_32"]

val ONE_LE_TWOEXP = store_thm(
  "ONE_LE_TWOEXP",
  ``1n <= 2 ** m``,
  SRW_TAC [][DECIDE ``1n <= x = 0 < x``]);
val _ = export_rewrites ["ONE_LE_TWOEXP"]

val w2i_n2w_pos = store_thm(
  "w2i_n2w_pos",
  ``&n <= INT_MAX (UNIV:'a set) ==>
    (w2i (n2w n : bool ** 'a) = &n)``,
  SRW_TAC [][w2i_def, word_msb_n2w, bitTheory.BIT_def, INT_SUB,
             bitTheory.BITS_def, DECIDE ``SUC x - x = 1``,
             bitTheory.DIV_2EXP_def, bitTheory.MOD_2EXP_def,
             w2n_n2w, INT_MAX_def, bitTheory.ZERO_LT_TWOEXP,
             DECIDE ``0n < y ==> (x <= y - 1 = x < y)``] THEN
  FULL_SIMP_TAC (srw_ss()) [LESS_DIV_EQ_ZERO] THEN
  MATCH_MP_TAC LESS_TRANS THEN
  Q.EXISTS_TAC `2 ** (dimindex (UNIV:'a set) - 1)` THEN
  SRW_TAC [ARITH_ss][DIMINDEX_GT_0, bitTheory.TWOEXP_MONO]);

val w2i_n2w_neg = store_thm(
  "w2i_n2w_neg",
  ``INT_MAX (UNIV: 'a set) < &n /\ n <= UINT_MAX (UNIV: 'a set) ==>
      (w2i (n2w n : bool ** 'a) =
          ~(2 ** dimindex (UNIV: 'a set) - &n))``,
  SRW_TAC [][w2i_def, word_msb_n2w, bitTheory.BIT_def, INT_SUB,
             bitTheory.BITS_def, DECIDE ``SUC x - x = 1``,
             bitTheory.DIV_2EXP_def, bitTheory.MOD_2EXP_def,
             w2n_n2w, word_2comp_n2w, INT_MAX_def, UINT_MAX_def,
             DECIDE ``0n < y ==> (x <= y - 1 = x < y)``]
  THENL [
    SRW_TAC [ARITH_ss][GSYM INT_SUB],
    `n DIV 2 ** (dimindex (UNIV: 'a set) - 1) = 1`
       by (MATCH_MP_TAC DIV_UNIQUE THEN
           Q.EXISTS_TAC `n - 2 ** (dimindex (UNIV: 'a set) - 1)` THEN
           SRW_TAC [ARITH_ss][bitTheory.ZERO_LT_TWOEXP] THEN
           SRW_TAC [][GSYM (CONJUNCT2 EXP)] THEN
           Q_TAC SUFF_TAC `SUC (dimindex (UNIV: 'a set) - 1) =
                           dimindex (UNIV: 'a set)` THEN1 SRW_TAC [][] THEN
           Q_TAC SUFF_TAC `0 < dimindex (UNIV: 'a set)` THEN1 DECIDE_TAC THEN
           SRW_TAC [][DIMINDEX_GT_0]) THEN
    FULL_SIMP_TAC (srw_ss()) []
  ]);


val i2w_w2i = store_thm(
  "i2w_w2i",
  ``i2w (w2i w) = w``,
  SRW_TAC [][w2i_def, i2w_def, n2w_w2n] THEN
  FULL_SIMP_TAC (srw_ss()) []);


val w2i_i2w = store_thm(
  "w2i_i2w",
  ``INT_MIN (UNIV : 'a set) <= i /\
    i <= INT_MAX (UNIV : 'a set)
      ==>
    (w2i (i2w i : bool ** 'a) = i)``,
  SIMP_TAC (srw_ss()) [INT_MIN_def, INT_MAX_def] THEN
  Q.ABBREV_TAC `WL = 2n ** dimindex (UNIV : 'a set)` THEN
  Q.ABBREV_TAC `HB = 2n ** (dimindex (UNIV : 'a set) - 1)` THEN
  `WL = 2 * HB`
     by (SRW_TAC [][Abbr`WL`, Abbr`HB`] THEN
         `0 < dimindex (UNIV : 'a set)` by SRW_TAC [][DIMINDEX_GT_0] THEN
         `?m. dimindex (UNIV : 'a set) = SUC m` by intLib.ARITH_TAC THEN
         SRW_TAC [][EXP]) THEN
  `0 < WL` by SRW_TAC [][Abbr`WL`, DIMINDEX_GT_0] THEN
  `1 <= HB /\ 1 <= WL` by SRW_TAC [][Abbr`WL`, Abbr`HB`] THEN
  ASM_SIMP_TAC (srw_ss()) [w2i_def, i2w_def, WORD_NEG_NEG, word_2comp_n2w,
                           INT_LE, INT_SUB, INT_LE_SUB_RADD,
                           NOT_LESS_EQUAL] THEN
  Cases_on `i < 0` THENL [
    `?n. ~(n = 0) /\ (i = ~&n)`
       by (Q.SPEC_THEN `i` STRIP_ASSUME_TAC INT_NUM_CASES THEN
           FULL_SIMP_TAC (srw_ss()) []) THEN
    ASM_SIMP_TAC (srw_ss()) [word_msb_n2w_numeric, word_2comp_n2w] THEN
    STRIP_TAC THEN
    `n MOD (2 * HB) = n` by (MATCH_MP_TAC MOD_UNIQUE THEN
                             Q.EXISTS_TAC `0` THEN DECIDE_TAC) THEN
    `2 * HB - n < 2 * HB` by DECIDE_TAC THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [LESS_MOD],

    `?n. i = &n`
       by (Q.SPEC_THEN `i` STRIP_ASSUME_TAC INT_NUM_CASES THEN
           FULL_SIMP_TAC (srw_ss()) []) THEN
    ASM_SIMP_TAC (srw_ss()) [word_msb_n2w_numeric, word_2comp_n2w] THEN
    STRIP_TAC THEN
    `n MOD (2 * HB) = n` by (MATCH_MP_TAC MOD_UNIQUE THEN
                             Q.EXISTS_TAC `0` THEN DECIDE_TAC) THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) []
  ])

val _ = export_theory()

