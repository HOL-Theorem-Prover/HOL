open HolKernel boolLib Parse bossLib BasicProvers

open wordsTheory wordsLib integerTheory intLib arithmeticTheory

(* theory of 2's complement representation of integers *)

val _ = new_theory "integer_word"

val i2w_def = Define`
  i2w (i : int) : 'a word =
    if i < 0 then -(n2w (Num(-i))) else n2w (Num i)
`;

val w2i_def = Define`
  w2i w = if word_msb w then ~(int_of_num (w2n (word_2comp w)))
          else int_of_num (w2n w)
`;

val UINT_MAX_def = Define`
  UINT_MAX (:'a) :int = &(dimword(:'a)) - 1
`;

val INT_MAX_def = Define`
  INT_MAX (:'a) :int = &(words$INT_MIN(:'a)) - 1
`;
val INT_MIN_def = Define`
  INT_MIN(:'a) = ~INT_MAX(:'a) - 1
`

val INT_MAX_32 = store_thm(
  "INT_MAX_32",
  ``INT_MAX (:32) = 2147483647``,
  SRW_TAC [][INT_MAX_def, dimindex_32, wordsTheory.INT_MIN_def]);
val _ = export_rewrites ["INT_MAX_32"]

val INT_MIN_32 = store_thm(
  "INT_MIN_32",
  ``INT_MIN (:32) = ~2147483648``,
  SRW_TAC [][INT_MIN_def]);
val _ = export_rewrites ["INT_MIN_32"]

val UINT_MAX_32 = store_thm(
  "UINT_MAX_32",
  ``UINT_MAX (: 32) = 4294967295``,
  SRW_TAC [][UINT_MAX_def, dimindex_32, dimword_def]);
val _ = export_rewrites ["UINT_MAX_32"]

val ONE_LE_TWOEXP = store_thm(
  "ONE_LE_TWOEXP",
  ``1n <= 2 ** m``,
  SRW_TAC [][DECIDE ``1n <= x = 0 < x``]);
val _ = export_rewrites ["ONE_LE_TWOEXP"]

val w2i_n2w_pos = store_thm(
  "w2i_n2w_pos",
  ``n < INT_MIN (:'a) ==>
    (w2i (n2w n : bool ** 'a) = &n)``,
  SRW_TAC [][w2i_def, word_msb_n2w, bitTheory.BIT_def, INT_SUB, dimword_def,
             bitTheory.BITS_def, DECIDE ``SUC x - x = 1``,
             wordsTheory.INT_MIN_def, DIV_2EXP_def, MOD_2EXP_def,
             w2n_n2w, INT_MAX_def, bitTheory.ZERO_LT_TWOEXP,
             DECIDE ``0n < y ==> (x <= y - 1 = x < y)``] THEN
  FULL_SIMP_TAC (srw_ss()) [LESS_DIV_EQ_ZERO] THEN
  MATCH_MP_TAC LESS_TRANS THEN
  Q.EXISTS_TAC `2 ** (dimindex (:'a) - 1)` THEN
  SRW_TAC [ARITH_ss][DIMINDEX_GT_0, bitTheory.TWOEXP_MONO]);

val w2i_n2w_neg = store_thm(
  "w2i_n2w_neg",
  ``INT_MIN (:'a) <= n /\ n < dimword (:'a) ==>
      (w2i (n2w n : 'a word) = ~ &(dimword(:'a) - n))``,
  SRW_TAC [ARITH_ss][w2i_def, word_msb_n2w, bitTheory.BIT_def, dimword_def,
                     bitTheory.BITS_def, DECIDE ``SUC x - x = 1``,
                     wordsTheory.INT_MIN_def, DIV_2EXP_def, MOD_2EXP_def,
                     w2n_n2w, word_2comp_n2w]
  THENL [
    Q_TAC SUFF_TAC `0n < 2 ** (dimindex (:'a) - 1)` THEN1 DECIDE_TAC THEN
    SRW_TAC [][],

    Q_TAC SUFF_TAC
          `~(2 ** (dimindex(:'a) - 1) <= n /\ n < 2 ** dimindex(:'a))`
          THEN1 METIS_TAC [] THEN STRIP_TAC THEN
    `n DIV 2 ** (dimindex (:'a) - 1) = 1`
       by (MATCH_MP_TAC DIV_UNIQUE THEN
           Q.EXISTS_TAC `n - 2 ** (dimindex (:'a) - 1)` THEN
           SRW_TAC [ARITH_ss][bitTheory.ZERO_LT_TWOEXP] THEN
           SRW_TAC [][GSYM (CONJUNCT2 EXP)] THEN
           Q_TAC SUFF_TAC `SUC (dimindex (:'a) - 1) =
                           dimindex (:'a)` THEN1 SRW_TAC [][] THEN
           Q_TAC SUFF_TAC `0 < dimindex (:'a)` THEN1 DECIDE_TAC THEN
           SRW_TAC [][DIMINDEX_GT_0]) THEN
    FULL_SIMP_TAC (srw_ss()) []
  ]);

val i2w_w2i = store_thm(
  "i2w_w2i",
  ``i2w (w2i w) = w``,
  SRW_TAC [][i2w_def, w2i_def] THEN FULL_SIMP_TAC (srw_ss()) [])

val w2i_i2w = store_thm(
  "w2i_i2w",
  ``INT_MIN (:'a) <= i /\ i <= INT_MAX (:'a)
      ==>
    (w2i (i2w i : 'a word) = i)``,
  SIMP_TAC (srw_ss()) [INT_MIN_def, INT_MAX_def] THEN
  `dimword(:'a) = 2 * INT_MIN(:'a)` by ACCEPT_TAC dimword_IS_TWICE_INT_MIN THEN
  `0 < dimword(:'a)` by ACCEPT_TAC ZERO_LT_dimword THEN
  `1n <= INT_MIN(:'a) /\ 1 <= dimword(:'a)` by DECIDE_TAC THEN
  ASM_SIMP_TAC std_ss [w2i_def, i2w_def, WORD_NEG_NEG, word_2comp_n2w,
                       INT_LE, INT_SUB, INT_LE_SUB_RADD,
                       NOT_LESS_EQUAL] THEN
  Cases_on `i < 0` THENL [
    `?n. ~(n = 0) /\ (i = ~&n)`
       by (Q.SPEC_THEN `i` STRIP_ASSUME_TAC INT_NUM_CASES THEN
           FULL_SIMP_TAC (srw_ss()) []) THEN
    ASM_SIMP_TAC std_ss [word_msb_n2w_numeric, word_2comp_n2w] THEN
    ASM_SIMP_TAC (srw_ss()) [] THEN
    STRIP_TAC THEN
    `n MOD (2 * INT_MIN(:'a)) = n` by (MATCH_MP_TAC MOD_UNIQUE THEN
                                   Q.EXISTS_TAC `0` THEN DECIDE_TAC) THEN
    `2 * INT_MIN(:'a) - n < 2 * INT_MIN(:'a)` by DECIDE_TAC THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [LESS_MOD],

    `?n. i = &n`
       by (Q.SPEC_THEN `i` STRIP_ASSUME_TAC INT_NUM_CASES THEN
           FULL_SIMP_TAC (srw_ss()) []) THEN
    ASM_SIMP_TAC (srw_ss()) [word_msb_n2w_numeric, word_2comp_n2w] THEN
    STRIP_TAC THEN
    `n MOD (2 * INT_MIN(:'a)) = n` by (MATCH_MP_TAC MOD_UNIQUE THEN
                                   Q.EXISTS_TAC `0` THEN DECIDE_TAC) THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) []
  ])

val word_msb_i2w = store_thm(
  "word_msb_i2w",
  ``word_msb (i2w i : 'a word) = &(INT_MIN(:'a)) <= i % &(dimword(:'a))``,
  `dimword(:'a) = 2 * INT_MIN(:'a)` by ACCEPT_TAC dimword_IS_TWICE_INT_MIN THEN
  `0 < dimword(:'a)` by ACCEPT_TAC ZERO_LT_dimword THEN
  `1n <= INT_MIN(:'a) /\ 1 <= dimword(:'a)` by DECIDE_TAC THEN
  ASM_SIMP_TAC (srw_ss()) [i2w_def] THEN
  Cases_on `i < 0` THENL [
    `?n. (i = ~&n) /\ ~(n = 0)`
        by (Q.SPEC_THEN `i` STRIP_ASSUME_TAC INT_NUM_CASES THEN
            FULL_SIMP_TAC (srw_ss()) []) THEN
    `n MOD (2 * INT_MIN(:'a)) < 2 * INT_MIN(:'a)` by SRW_TAC [ARITH_ss][DIVISION] THEN
    `~(&(2 * INT_MIN(:'a)) = 0)` by SRW_TAC [ARITH_ss][] THEN
    `(& (2 * INT_MIN(:'a)) - &n) % &(2 * INT_MIN(:'a)) =
        (&(2 * INT_MIN(:'a)) - &n % &(2 * INT_MIN(:'a))) % &(2 * INT_MIN(:'a))`
       by METIS_TAC [INT_MOD_MOD, INT_MOD_SUB] THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [word_2comp_n2w, word_msb_n2w_numeric,
                                         INT_MOD_NEG_NUMERATOR, INT_MOD,
                                         INT_SUB],

    `?n. (i = &n)`
        by (Q.SPEC_THEN `i` STRIP_ASSUME_TAC INT_NUM_CASES THEN
            FULL_SIMP_TAC (srw_ss()) []) THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [word_msb_n2w_numeric, INT_MOD]
  ])

val w2i_11 = store_thm("w2i_11",
  ``!v w. (w2i v = w2i w) = (v = w)``,
  NTAC 2 STRIP_TAC THEN EQ_TAC
    THEN SRW_TAC [] [SIMP_RULE (srw_ss()) [] WORD_EQ_NEG, w2i_def]);

val WORD_LTi = store_thm("WORD_LTi",
  ``!a b. a < b = w2i a < w2i b``,
  RW_TAC std_ss [WORD_LT, GSYM WORD_LO, INT_LT_CALCULATE, WORD_NEG_EQ_0,
                 w2i_def, w2n_eq_0]
    THENL [
      SRW_TAC [boolSimps.LET_ss] [word_lo_def,nzcv_def,
               Once (DECIDE ``w2n (-b) + a = a + w2n (-b)``)]
        THEN Cases_on `~BIT (dimindex (:'a)) (w2n a + w2n (-b))`
        THEN FULL_SIMP_TAC std_ss [] ,
      DISJ1_TAC]
    THEN FULL_SIMP_TAC (std_ss++fcpLib.FCP_ss) [word_0, word_msb_def]
    THEN METIS_TAC [DECIDE ``0n < n ==> n - 1 < n``, DIMINDEX_GT_0]);

val WORD_GTi = store_thm("WORD_GTi",
  ``!a b. a > b = w2i a > w2i b``,
  REWRITE_TAC [WORD_GREATER, int_gt, WORD_LTi]);

val WORD_LEi = store_thm("WORD_LEi",
  ``!a b. a <= b = w2i a <= w2i b``,
  REWRITE_TAC [WORD_LESS_OR_EQ, INT_LE_LT, WORD_LTi, w2i_11]);

val WORD_GEi = store_thm("WORD_GEi",
  ``!a b. a >= b = w2i a >= w2i b``,
  REWRITE_TAC [WORD_GREATER_EQ, int_ge, WORD_LEi]);

val sum_num = intLib.COOPER_PROVE
  ``(Num (&a + &b) = a + b) /\
    (-&a + -&b = -&(a + b)) /\
    ~(&a + &b < 0i) /\
    (-&a + &b < 0i = b < a:num) /\
    (&a + -&b < 0i = a < b:num) /\
    (&a - &b < 0i = a < b:num) /\
    (~(&a + -&b < 0i) = b <= a:num) /\
    (~(-&a + &b < 0i) = a <= b:num) /\
    (~(&a - &b < 0i) = b <= a:num) /\
    (~(-&a - &b < 0i) = (a = 0) /\ (b = 0))``;

val word_literal_sub =
  METIS_PROVE [arithmeticTheory.NOT_LESS_EQUAL, WORD_LITERAL_ADD]
    ``(m < n ==> (-n2w (n - m) = n2w m + -n2w n)) /\
      (n <= m ==> (n2w (m - n) = n2w m + -n2w n))``;

val word_add_i2w_w2n = Q.store_thm("word_add_i2w_w2n",
  `!a b. i2w (&w2n a + &w2n b) = a + b`,
  SRW_TAC [] [i2w_def, word_add_def, sum_num]);

val word_add_i2w = Q.store_thm("word_add_i2w",
  `!a b. i2w (w2i a + w2i b) = a + b`,
  SRW_TAC [] [i2w_def, w2i_def]
  THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss)
         [WORD_LEFT_ADD_DISTRIB, GSYM word_add_def, sum_num, word_literal_sub,
          intLib.COOPER_PROVE
              ``(&y < &x ==> (Num (-(-&x + &y)) = x - y)) /\
                (&x < &y ==> (Num (-(&x + -&y)) = y - x)) /\
                (~(&y < &x) ==> (Num (-&x + &y) = y - x)) /\
                (~(&x < &y) ==> (Num (&x + -&y) = x - y))``]);

val word_sub_i2w_w2n = Q.store_thm("word_sub_i2w_w2n",
  `!a b. i2w (&w2n a - &w2n b) = a - b`,
  SRW_TAC [] [i2w_def, intLib.COOPER_PROVE
          ``(&x - &y < 0i ==> (Num ((&y - &x)) = y - x)) /\
            (~(&x - &y < 0i) ==> (Num ((&x - &y)) = x - y))``]
  THEN FULL_SIMP_TAC (srw_ss()) [sum_num, word_literal_sub]);

val word_sub_i2w = Q.store_thm("word_sub_i2w",
  `!a b. i2w (w2i a - w2i b) = a - b`,
  SRW_TAC [] [i2w_def, w2i_def]
  THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss)
         [WORD_LEFT_ADD_DISTRIB, GSYM word_add_def, sum_num, word_literal_sub,
          intLib.COOPER_PROVE
              ``(&x < &y ==> (Num (&y - &x) = y - x)) /\
                (~(&x < &y) ==> (Num (&x - &y) = x - y))``]);

val _ = export_theory()
