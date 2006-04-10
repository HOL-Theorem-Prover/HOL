open HolKernel boolLib Parse bossLib BasicProvers

open wordsTheory integerTheory

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
  INT_MAX (x: 'a set) = 2n ** (dimindex (UNIV: 'a set) - 1) - 1
`;

val INT_MAX_32 = store_thm(
  "INT_MAX_32",
  ``INT_MAX (s: i32 set) = 2147483647``,
  SRW_TAC [][INT_MAX_def, dimindex_32]);
val _ = export_rewrites ["INT_MAX_32"]

val UINT_MAX_32 = store_thm(
  "UINT_MAX_32",
  ``UINT_MAX (s: i32 set) = 4294967295``,
  SRW_TAC [][UINT_MAX_def, dimindex_32]);
val _ = export_rewrites ["UINT_MAX_32"]

val w2i_n2w_pos = store_thm(
  "w2i_n2w_pos",
  ``x <= INT_MAX (UNIV:'a set) ==>
    (w2i (n2w x : bool ** 'a) = int_of_num x)``,
  SRW_TAC [][w2i_def, word_msb_n2w, bitTheory.BIT_def,
             bitTheory.BITS_def, DECIDE ``SUC x - x = 1``,
             bitTheory.DIV_2EXP_def, bitTheory.MOD_2EXP_def,
             w2n_n2w, INT_MAX_def, bitTheory.ZERO_LT_TWOEXP,
             DECIDE ``0n < y ==> (x <= y - 1 = x < y)``] THEN
  FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.LESS_DIV_EQ_ZERO] THEN
  MATCH_MP_TAC arithmeticTheory.LESS_TRANS THEN
  Q.EXISTS_TAC `2 ** (dimindex (UNIV:'a set) - 1)` THEN
  SRW_TAC [ARITH_ss][DIMINDEX_GT_0, bitTheory.TWOEXP_MONO]);

val w2i_n2w_neg = store_thm(
  "w2i_n2w_neg",
  ``INT_MAX (UNIV: 'a set) < x /\ x <= UINT_MAX (UNIV: 'a set) ==>
      (w2i (n2w x : bool ** 'a) =
          ~(2 ** dimindex (UNIV: 'a set) - int_of_num x))``,
  SRW_TAC [][w2i_def, word_msb_n2w, bitTheory.BIT_def,
             bitTheory.BITS_def, DECIDE ``SUC x - x = 1``,
             bitTheory.DIV_2EXP_def, bitTheory.MOD_2EXP_def,
             w2n_n2w, word_2comp_n2w, INT_MAX_def, UINT_MAX_def,
             bitTheory.ZERO_LT_TWOEXP,
             DECIDE ``0n < y ==> (x <= y - 1 = x < y)``]
  THENL [
    SRW_TAC [ARITH_ss][GSYM INT_SUB],
    `x DIV 2 ** (dimindex (UNIV: 'a set) - 1) = 1`
       by (MATCH_MP_TAC arithmeticTheory.DIV_UNIQUE THEN
           Q.EXISTS_TAC `x - 2 ** (dimindex (UNIV: 'a set) - 1)` THEN
           SRW_TAC [ARITH_ss][bitTheory.ZERO_LT_TWOEXP] THEN
           SRW_TAC [][GSYM (CONJUNCT2 arithmeticTheory.EXP)] THEN
           Q_TAC SUFF_TAC `SUC (dimindex (UNIV: 'a set) - 1) =
                           dimindex (UNIV: 'a set)` THEN1 SRW_TAC [][] THEN
           Q_TAC SUFF_TAC `0 < dimindex (UNIV: 'a set)` THEN1 DECIDE_TAC THEN
           SRW_TAC [][DIMINDEX_GT_0]) THEN
    FULL_SIMP_TAC (srw_ss()) []
  ]);


val i2w_w2i = store_thm(
  "i2w_w2i",
  ``i2w (w2i w) = w``,
  SRW_TAC [][w2i_def, i2w_def, n2w_w2n, WORD_NEG_NEG] THEN
  FULL_SIMP_TAC (srw_ss()) [w2n_eq_0, WORD_NEG_EQ_0, WORD_NEG_0,
                            w2n_n2w, bitTheory.ZERO_LT_TWOEXP]);





val _ = export_theory()

