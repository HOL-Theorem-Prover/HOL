open HolKernel boolLib Parse bossLib BasicProvers

open bitTheory wordsTheory wordsLib integerTheory intLib arithmeticTheory

(* theory of 2's complement representation of integers *)

infix \\
val op \\ = op THEN;

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

val ONE_LE_TWOEXP = save_thm("ONE_LE_TWOEXP", bitTheory.ONE_LE_TWOEXP);

val w2i_w2n_pos = Q.store_thm("w2i_w2n_pos",
  `!w n. ~word_msb w /\ w2i w < &n ==> w2n w < n`,
  SRW_TAC [] [w2i_def]);

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

val int_word_nchotomy = Q.store_thm("int_word_nchotomy",
  `!w. ?i. w = i2w i`, PROVE_TAC [i2w_w2i]);

val w2i_le = Q.store_thm("w2i_le",
  `!w:'a word. w2i w <= INT_MAX (:'a)`,
  SRW_TAC [] [w2i_def, INT_MAX_def, ZERO_LT_INT_MIN,
       intLib.ARITH_PROVE ``0n < i ==> 0 <= &i - 1``,
       intLib.ARITH_PROVE ``0i <= x ==> -&n <= x``]
  THEN FULL_SIMP_TAC arith_ss [dimword_def, wordsTheory.INT_MIN_def,
       WORD_LO, WORD_NOT_LOWER_EQUAL, WORD_MSB_INT_MIN_LS, word_L_def,
       w2n_n2w, LESS_MOD, EXP_BASE_LT_MONO, DIMINDEX_GT_0]
  THEN intLib.ARITH_TAC);

val w2i_ge = Q.store_thm("w2i_ge",
  `!w:'a word. INT_MIN (:'a) <= w2i w`,
  Tactical.REVERSE (SRW_TAC []
    [w2i_def, INT_MIN_def, INT_MAX_def, INT_SUB_LNEG, INT_LE_REDUCE])
  THEN1 intLib.ARITH_TAC
  THEN IMP_RES_TAC TWO_COMP_NEG
  THEN POP_ASSUM MP_TAC
  THEN SRW_TAC [] []
  THEN FULL_SIMP_TAC std_ss []
  THENL [
    Cases_on `w`
    THEN `dimindex(:'a) = 1` by FULL_SIMP_TAC arith_ss [DIMINDEX_GT_0]
    THEN FULL_SIMP_TAC std_ss [dimword_def, wordsTheory.INT_MIN_def]
    THEN `(n = 0) \/ (n = 1)` by DECIDE_TAC
    THEN SRW_TAC [] [dimword_def, word_2comp_def],
    REWRITE_TAC [GSYM WORD_NEG_MUL, WORD_NEG_L]
    THEN SRW_TAC [] [word_L_def, w2n_n2w, INT_MIN_LT_DIMWORD, LESS_MOD],
    Q.ABBREV_TAC `x = -1w * w`
    THEN FULL_SIMP_TAC arith_ss [dimword_def, wordsTheory.INT_MIN_def,
         WORD_LO, WORD_NOT_LOWER_EQUAL, WORD_MSB_INT_MIN_LS, word_L_def,
         w2n_n2w, LESS_MOD, EXP_BASE_LT_MONO, DIMINDEX_GT_0]
  ]);

val ranged_int_word_nchotomy = Q.store_thm("ranged_int_word_nchotomy",
  `!w:'a word. ?i. (w = i2w i) /\ INT_MIN (:'a) <= i /\ i <= INT_MAX (:'a)`,
  STRIP_TAC THEN Q.EXISTS_TAC `w2i w`
  THEN SRW_TAC [] [i2w_w2i, w2i_le, w2i_ge]);

fun Cases_on_i2w t =
  Tactic.FULL_STRUCT_CASES_TAC (Q.ISPEC t ranged_int_word_nchotomy);

val DIMINDEX_SUB1 = Q.prove(
  `2n ** (dimindex (:'a) - 1) < 2 ** dimindex (:'a)`,
  Cases_on `dimindex (:'a)` \\ FULL_SIMP_TAC arith_ss [DIMINDEX_GT_0]);

val lem = Q.prove(
  `!i. INT_MIN (:'a) <= i /\ i < 0 ==> Num (-i) <= INT_MIN (:'a)`,
  SRW_TAC [] [INT_MIN_def, INT_MAX_def, wordsTheory.INT_MIN_def]
  \\ Cases_on `dimindex (:'a)`
  \\ FULL_SIMP_TAC arith_ss [DIMINDEX_GT_0]
  \\ intLib.ARITH_TAC);

val lem2 = Q.prove(
  `!i. INT_MIN (:'a) <= i /\ i < 0 ==> Num (-i) < dimword(:'a)`,
  METIS_TAC [lem, wordsTheory.INT_MIN_LT_DIMWORD,
             arithmeticTheory.LESS_EQ_LESS_TRANS]);

val NEG_INT_ELIM = Q.prove(
  `!i. INT_MIN (:'a) <= i /\ i < 0 /\ dimindex (:'a) <= dimindex(:'b) ==>
       ?n. INT_MIN (:'a) <= n /\ n < dimword (:'a) /\
           (-n2w (Num (-i)) = n2w n : 'a word) /\
           (-n2w (Num (-i)) =
               n2w (2 ** dimindex (:'b) - 2 ** dimindex (:'a) + n) : 'b word)`,
  REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `dimword (:'a) - Num (-i)`
  \\ SRW_TAC [ARITH_ss]
        [wordsTheory.ONE_LT_dimword, ZERO_LT_INT_MIN, word_2comp_def, lem2]
  \\ IMP_RES_TAC lem
  THENL [
    ASM_SIMP_TAC arith_ss
      [wordsTheory.dimword_IS_TWICE_INT_MIN, wordsTheory.ZERO_LT_INT_MIN],
    intLib.ARITH_TAC,
    FULL_SIMP_TAC arith_ss [dimword_def, wordsTheory.INT_MIN_def]
    \\ `2n ** dimindex (:'a) <= 2 ** dimindex (:'b)`
    by METIS_TAC [bitTheory.TWOEXP_MONO2]
    \\ `Num (-i) < 2n ** dimindex (:'a) /\
        Num (-i) < 2n ** dimindex (:'b)`
    by METIS_TAC [DIMINDEX_SUB1, arithmeticTheory.LESS_EQ_LESS_TRANS,
                  arithmeticTheory.LESS_LESS_EQ_TRANS]
    \\ ASM_SIMP_TAC arith_ss [bitTheory.ZERO_LT_TWOEXP,
          DECIDE ``c < b /\ b <= a ==> (a - b + (b - c) = a - c : num)``,
          wordsTheory.MOD_COMPLEMENT |> Q.SPECL [`n`,`1`] |> GSYM
          |> REWRITE_RULE [arithmeticTheory.MULT_LEFT_1]]
  ]);

val sw2sw_i2w = Q.store_thm("sw2sw_i2w",
  `!j. INT_MIN (:'b) <= j /\ j <= INT_MAX (:'b) /\
       dimindex (:'b) <= dimindex (:'a) ==>
       (sw2sw (i2w j : 'b word) = i2w j : 'a word)`,
  SRW_TAC [WORD_BIT_EQ_ss] [i2w_def]
  THENL [
    `?n. INT_MIN (:'b) <= n /\ n < dimword (:'b) /\
         (-n2w (Num (-j)) = n2w n : 'b word) /\
         (-n2w (Num (-j)) =
           n2w (2 ** dimindex (:'a) - 2 ** dimindex (:'b) + n) : 'a word)`
    by METIS_TAC [NEG_INT_ELIM]
    \\ SRW_TAC [fcpLib.FCP_ss,ARITH_ss] [word_index, BIT_def]
    THENL [
      `2n ** dimindex (:'a) MOD 2 ** SUC i = 0`
      by (`?k. dimindex (:'a) = k + SUC i`
          by METIS_TAC [LESS_ADD_1, ADD_COMM, ADD_ASSOC, ADD1]
          \\ ASM_SIMP_TAC arith_ss
               [EXP_ADD, bitTheory.ZERO_LT_TWOEXP, MOD_EQ_0])
      \\ `2n ** dimindex (:'b) MOD 2 ** SUC i = 0`
      by (`?k. dimindex (:'b) = k + SUC i`
          by METIS_TAC [LESS_ADD_1, ADD_COMM, ADD_ASSOC, ADD1]
          \\ ASM_SIMP_TAC arith_ss
               [EXP_ADD, bitTheory.ZERO_LT_TWOEXP, MOD_EQ_0])
      \\ `2n ** dimindex (:'a) - 2 ** dimindex (:'b) =
          (2n ** (dimindex (:'a) - SUC i) -
           2n ** (dimindex (:'b) - SUC i)) * 2 ** SUC i`
      by SRW_TAC [ARITH_ss]
            [arithmeticTheory.RIGHT_SUB_DISTRIB, arithmeticTheory.EXP_SUB,
             bitTheory.DIV_MULT_THM]
      \\ ASM_SIMP_TAC std_ss [bitTheory.BITS_SUM2],
      FULL_SIMP_TAC std_ss [NOT_LESS]
      \\ `2n ** dimindex (:'a) MOD 2 ** i = 0`
      by (`?k. dimindex (:'a) = k + i` by METIS_TAC [LESS_ADD]
          \\ ASM_SIMP_TAC std_ss [EXP_ADD, bitTheory.ZERO_LT_TWOEXP, MOD_EQ_0])
      \\ `2n ** i < 2 ** dimindex (:'a) /\
          2n ** dimindex (:'b) <= 2 ** i`
      by METIS_TAC [bitTheory.TWOEXP_MONO, bitTheory.TWOEXP_MONO2]
      \\ `2n ** dimindex (:'a) - 2 ** dimindex (:'b) =
          (2n ** (dimindex (:'a) - i) - 1) * 2 ** i +
          (2 ** i - 2 ** dimindex (:'b))`
      by SRW_TAC [ARITH_ss]
            [arithmeticTheory.RIGHT_SUB_DISTRIB, arithmeticTheory.EXP_SUB,
             bitTheory.DIV_MULT_THM,
             DECIDE ``b < a /\ c <= b ==> (a - b + (b - c) = a - c : num)``]
      \\ `2n ** i - 2 ** dimindex (:'b) + n < 2 ** i`
      by METIS_TAC [dimword_def, bitTheory.TWOEXP_MONO2,
            DECIDE ``b <= a /\ c < b ==> a - b + c < a : num``]
      \\ ASM_SIMP_TAC std_ss [GSYM ADD_ASSOC, bitTheory.BITS_SUM,
           bitTheory.BITS_ZERO4, REWRITE_RULE [BIT_def] bitTheory.BIT_EXP_SUB1]
      \\ NTAC 8 (POP_ASSUM (K ALL_TAC))
      \\ ASM_SIMP_TAC arith_ss []
      \\ `?m. m < 2 ** (dimindex (:'b) - 1) /\
              (n = 1 * 2 ** (dimindex (:'b) - 1) + m)`
      by
       (FULL_SIMP_TAC std_ss [wordsTheory.INT_MIN_def]
        \\ Q.PAT_ASSUM `2n ** x <= n` (fn th => STRIP_ASSUME_TAC
             (MATCH_MP arithmeticTheory.LESS_EQUAL_ADD th))
        \\ Q.EXISTS_TAC `p`
        \\ SRW_TAC [] []
        \\ `2 ** (dimindex (:'b) - 1) + 2 ** (dimindex (:'b) - 1) =
            dimword (:'b)`
        by (SIMP_TAC std_ss [dimword_def]
            \\ Cases_on `dimindex (:'b)`
            \\ SIMP_TAC arith_ss [EXP]
            \\ METIS_TAC [DIMINDEX_GT_0, DECIDE ``0n < n ==> ~(n = 0)``])
        \\ FULL_SIMP_TAC arith_ss
              [DECIDE ``p + b < c /\ (b + b = c) ==> p < b : num``])
      \\ ASM_SIMP_TAC bool_ss [bitTheory.BITS_SUM]
      \\ SIMP_TAC std_ss [GSYM BIT_def, bitTheory.BIT_B]
    ],
    SRW_TAC [fcpLib.FCP_ss] [word_index]
    \\ `0 < i`
    by (SPOSE_NOT_THEN ASSUME_TAC \\ `dimindex (:'b) = 0` by DECIDE_TAC
        \\ METIS_TAC [DIMINDEX_GT_0, DECIDE ``(0n < i) = (i <> 0)``])
    \\ FULL_SIMP_TAC std_ss
         [INT_MAX_def, wordsTheory.INT_MIN_def, NOT_LESS,
          integerTheory.INT_NOT_LT, intLib.ARITH_PROVE ``x <= y - 1i = x < y``]
    \\ `Num j < 2n ** (dimindex (:'b) - 1)` by intLib.ARITH_TAC
    \\ `2n ** (dimindex (:'b) - 1) < 2 ** i` by SRW_TAC [ARITH_ss] []
    \\ `Num j < 2n ** i` by METIS_TAC [arithmeticTheory.LESS_TRANS]
    \\ ASM_SIMP_TAC std_ss [bitTheory.NOT_BIT_GT_TWOEXP]
  ]
);

val w2w_i2w = Q.store_thm("w2w_i2w",
  `!i. dimindex(:'a) <= dimindex(:'b) ==>
       (w2w (i2w i : 'b word) = i2w i : 'a word)`,
  SRW_TAC [] [i2w_def, wordsTheory.w2w_n2w, wordsTheory.word_2comp_def]
  \\ `?q. 0n < q /\ Num (-i) MOD (q * dimword (:'a)) < q * dimword (:'a) /\         (dimword (:'b) = q * dimword (:'a))`
  by (IMP_RES_TAC arithmeticTheory.LESS_EQUAL_ADD
      \\ Q.EXISTS_TAC `2n ** p`
      \\ FULL_SIMP_TAC arith_ss [ZERO_LT_TWOEXP, dimword_def, GSYM EXP_ADD])
  \\ ASM_SIMP_TAC arith_ss [wordsTheory.MOD_COMPLEMENT,
       wordsTheory.ZERO_LT_dimword,
       ONCE_REWRITE_RULE [MULT_COMM] arithmeticTheory.MOD_MULT_MOD]
  );

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

val word_mul_i2w_w2n = Q.store_thm("word_mul_i2w_w2n",
  `!a b. i2w (&w2n a * &w2n b) = a * b`,
  SRW_TAC [] [i2w_def]
  THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss)
         [GSYM word_mul_def, INT_MUL_CALCULATE]);

val word_mul_i2w = Q.store_thm("word_mul_i2w",
  `!a b. i2w (w2i a * w2i b) = a * b`,
  SRW_TAC [] [i2w_def, w2i_def]
  THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss)
         [GSYM word_mul_def, INT_MUL_CALCULATE]);

(* ------------------------------------------------------------------------- *)

val word_literal_sub =
  METIS_PROVE [arithmeticTheory.NOT_LESS_EQUAL, WORD_LITERAL_ADD]
    ``(m < n ==> (n2w m + -n2w n = -n2w (n - m))) /\
      (n <= m ==> (n2w m + -n2w n = n2w (m - n)))``;

val sum_num = intLib.ARITH_PROVE
  ``(a < 0 /\ b < 0 ==> (Num (-a) + Num (-b) = Num (-(a + b)))) /\
    (0 <= a /\ 0 <= b ==> (Num a + Num b = Num (a + b))) /\
    (0 <= b /\ a + b < 0 ==> (Num (-a) - Num b = Num (-(a + b)))) /\
    (a < 0 /\ 0 <= b /\ 0 <= a + b ==> (Num b - Num (-a) = Num (a + b))) /\
    (0 <= a /\ b < 0 /\ a + b < 0 ==> (Num (-b) - Num a = Num (-(a + b)))) /\
    (b < 0 /\ 0 <= a + b ==> (Num a - Num (-b) = Num (a + b)))``;

val word_i2w_add = Q.store_thm("word_i2w_add",
  `!a b. i2w a + i2w b = i2w (a + b)`,
  SRW_TAC [] [i2w_def, w2i_def]
  THEN FULL_SIMP_TAC (srw_ss()++INT_ARITH_ss)
        [integerTheory.INT_NOT_LT, word_add_n2w, word_literal_sub, sum_num,
         EQT_ELIM (wordsLib.WORD_ARITH_CONV
           ``(-a + -b = -c : 'a word) = (a + b = c)``)]
  THENL [
    `Num b < Num (-a)` by intLib.ARITH_TAC,
    `Num (-a) <= Num b` by intLib.ARITH_TAC,
    `Num a < Num (-b)` by intLib.ARITH_TAC,
    `Num (-b) <= Num a` by intLib.ARITH_TAC]
  THEN ASM_SIMP_TAC std_ss [word_literal_sub, sum_num]);

val mult_num = Q.prove(
  `(!i j. 0 <= i /\ 0 <= j ==> (Num i * Num j = Num (i * j))) /\
   (!i j. 0 <= i /\ j < 0 ==> (Num i * Num (-j) = Num (-(i * j))))`,
  STRIP_TAC THEN Cases_on `i` THEN Cases_on `j`
  THEN SRW_TAC [] [NUM_OF_INT, INT_NEG_RMUL]);

val mult_lt = Q.prove(
  `(!i:int j. 0 <= i /\ j < 0 ==> i * j <= 0) /\
   (!i:int j. i < 0 /\ 0 <= j ==> i * j <= 0)`,
  STRIP_TAC THEN Cases_on `i` THEN Cases_on `j`
  THEN SRW_TAC [] [NUM_OF_INT, INT_MUL_CALCULATE]);

val word_i2w_mul = Q.store_thm("word_i2w_mul",
  `!a b. i2w a * i2w b = i2w (a * b)`,
  SRW_TAC [] [i2w_def, w2i_def]
  THEN FULL_SIMP_TAC (srw_ss()++INT_ARITH_ss)
        [integerTheory.INT_NOT_LT, word_mul_n2w, WORD_LITERAL_MULT, mult_num,
         integerTheory.INT_MUL_SIGN_CASES, INT_MUL_CALCULATE,
         AC INT_MUL_COMM INT_MUL_ASSOC]
  THEN IMP_RES_TAC mult_lt
  THEN `a * b = 0` by intLib.ARITH_TAC
  THEN ASM_SIMP_TAC (srw_ss()) []);

(* ------------------------------------------------------------------------- *)

val MINUS_ONE = Q.prove(`-1w = i2w (-1)`, SRW_TAC [] [i2w_def]);

val MULT_MINUS_ONE = Q.store_thm("MULT_MINUS_ONE",
  `!i. -1w * i2w i = i2w (-i)`,
  REWRITE_TAC [MINUS_ONE, word_i2w_mul, GSYM INT_NEG_MINUS1]);

val word_0_w2i = Q.store_thm("word_0_w2i",
  `w2i 0w = 0`,
  SRW_TAC [] [i2w_def, w2i_def]);

(* ------------------------------------------------------------------------- *)

val DIV_POS = Q.prove(
  `!i n. ~(i < 0) /\ 0n < n ==> ~(i / &n < 0)`,
  Cases \\ SRW_TAC [ARITH_ss] [integerTheory.INT_DIV_CALCULATE]);

val DIV_NEG = Q.prove(
  `!i n. i < 0i /\ 0n < n ==> i / &n < 0`,
  Cases \\ SRW_TAC [ARITH_ss] [integerTheory.INT_DIV_CALCULATE]
  \\ `&n' <> 0` by intLib.ARITH_TAC
  \\ SRW_TAC [] [integerTheory.int_div]
  THENL [
    Cases_on `n < n'`
    \\ FULL_SIMP_TAC arith_ss [NOT_LESS]
    \\ IMP_RES_TAC LESS_EQUAL_ADD
    \\ POP_ASSUM SUBST1_TAC
    \\ ASM_SIMP_TAC arith_ss [arithmeticTheory.ADD_DIV_RWT],
    intLib.ARITH_TAC
  ]);

val DIV_NUM_POS = Q.prove(
  `!i j. 0 < j /\ 0i <= i ==> (Num (i / &j) = Num i DIV j)`,
  Cases \\ SRW_TAC [ARITH_ss] [integerTheory.INT_DIV_CALCULATE]);

val DIV_NUM_NEG = Q.prove(
  `!i j. 0 < j /\ i < 0i ==>
         (Num (-(i / &j)) =
          Num (-i) DIV j + (if Num (-i) MOD j = 0 then 0 else 1))`,
  Cases \\ SRW_TAC [ARITH_ss] [integerTheory.INT_DIV_CALCULATE]
  \\ `&j <> 0` by intLib.ARITH_TAC
  \\ SRW_TAC [] [integerTheory.int_div, integerTheory.INT_NEG_ADD]
  \\ intLib.ARITH_TAC);

val NEG_NUM_LT_INT_MIN = Q.prove(
  `!i. INT_MIN (:'a) <= i /\ i < 0 ==> Num (-i) <= INT_MIN (:'a)`,
  SRW_TAC [] [INT_MIN_def, INT_MAX_def, wordsTheory.INT_MIN_def]
  \\ Cases_on `dimindex (:'a)`
  \\ FULL_SIMP_TAC arith_ss [DIMINDEX_GT_0]
  \\ intLib.ARITH_TAC);

val NEG_NUM_LT_DIMWORD = Q.prove(
  `!i. INT_MIN (:'a) <= i /\ i < 0 ==> Num (-i) < dimword(:'a)`,
  METIS_TAC [NEG_NUM_LT_INT_MIN, wordsTheory.INT_MIN_LT_DIMWORD,
             arithmeticTheory.LESS_EQ_LESS_TRANS]);

val NEG_MSB = Q.prove(
  `!i. i < 0i /\ INT_MIN (:'a) <= i ==>
      BIT (dimindex (:'a) - 1) (2 ** dimindex (:'a) - Num (-i))`,
  SRW_TAC [] [INT_MIN_def, INT_MAX_def, wordsTheory.INT_MIN_def]
  \\ `Num (-i) <= 2n ** (dimindex (:'a) - 1)` by intLib.ARITH_TAC
  \\ Cases_on `dimindex (:'a)`
  \\ FULL_SIMP_TAC arith_ss [wordsTheory.DIMINDEX_GT_0,
        DECIDE ``0n < n ==> n <> 0``]
  \\ IMP_RES_TAC LESS_EQUAL_ADD
  \\ `Num (-i) = 2 ** n - p` by DECIDE_TAC
  \\ POP_ASSUM SUBST1_TAC
  \\ `p < 2 ** n` by intLib.ARITH_TAC
  \\ Q.PAT_ASSUM `x = y + z : num` (K ALL_TAC)
  \\ ASM_SIMP_TAC bool_ss [EXP, BIT_def,
       DECIDE ``p < n ==> (2n * n - (n - p) = n + p)``,
       bitTheory.BITS_SUM |> Q.SPECL [`n`,`n`,`1`] |> SIMP_RULE std_ss []]
  \\ SIMP_TAC std_ss [GSYM BIT_def, bitTheory.BIT_B]);

val DIMINDEX_SUB1 = Q.prove(
  `2n ** (dimindex (:'a) - 1) < 2 ** dimindex (:'a)`,
  Cases_on `dimindex (:'a)` \\ FULL_SIMP_TAC arith_ss [DIMINDEX_GT_0]);

val i2w_DIV = Q.store_thm("i2w_DIV",
  `!n i.
     n < dimindex (:'a) /\ INT_MIN (:'a) <= i /\ i <= INT_MAX (:'a) ==>
     (i2w (i / 2 ** n) : 'a word = i2w i >> n)`,
  SRW_TAC [wordsLib.WORD_BIT_EQ_ss]
          [i2w_def, DIV_POS, word_2comp_n2w, DIV_NEG, word_index]
  \\ FULL_SIMP_TAC std_ss
          [DIV_NUM_POS, DIV_NUM_NEG, ZERO_LT_TWOEXP, integerTheory.INT_NOT_LT]
  THENL [
    IMP_RES_TAC NEG_NUM_LT_DIMWORD
    \\ FULL_SIMP_TAC std_ss [dimword_def]
    \\ `Num (-i) < 2n ** dimindex (:'a)` by intLib.ARITH_TAC
    \\ Cases_on `dimindex (:'a) <= i' + n`
    \\ FULL_SIMP_TAC arith_ss [arithmeticTheory.NOT_LESS_EQUAL, BIT_SHIFT_THM5]
    \\ `Num (-i) <> 0` by intLib.ARITH_TAC
    \\ SRW_TAC [ARITH_ss] [BIT_COMPLEMENT, NEG_MSB, DIV_LT]
    THENL [
      METIS_TAC [MOD_ZERO_GT, DIV_GT0, ZERO_LT_TWOEXP,
        DECIDE ``0n < x ==> (x <> 0)``],
      IMP_RES_TAC MOD_ZERO_GT
      \\ IMP_RES_TAC DIV_SUB1
      \\ `Num (-i) < 2 ** (i' + n)`
      by METIS_TAC [TWOEXP_MONO2, arithmeticTheory.LESS_LESS_EQ_TRANS]
      \\ `Num (-i) - 1 < 2n ** (i' + n)` by DECIDE_TAC
      \\ ASM_SIMP_TAC arith_ss [BIT_SHIFT_THM4, bitTheory.NOT_BIT_GT_TWOEXP],
      IMP_RES_TAC NEG_NUM_LT_INT_MIN
      \\ FULL_SIMP_TAC std_ss [wordsTheory.INT_MIN_def]
      \\ `1n < 2 ** n` by ASM_SIMP_TAC arith_ss [arithmeticTheory.ONE_LT_EXP]
      \\ `Num (-i) DIV 2 ** n < Num (-i)`
      by ASM_SIMP_TAC arith_ss [arithmeticTheory.DIV_LESS, ZERO_LT_TWOEXP]
      \\ `Num (-i) DIV 2 ** n + 1 <= Num (-i)` by DECIDE_TAC
      \\ `Num (-i) DIV 2 ** n + 1 < 2 ** dimindex (:'a)`
      by METIS_TAC [arithmeticTheory.LESS_EQ_TRANS,
                    arithmeticTheory.LESS_EQ_LESS_TRANS,
                    DIMINDEX_SUB1, TWOEXP_MONO]
      \\ ASM_SIMP_TAC arith_ss [],
      `Num (-i) < 2 ** (i' + n)`
      by METIS_TAC [TWOEXP_MONO2, arithmeticTheory.LESS_LESS_EQ_TRANS]
      \\ `1n < 2 ** n` by ASM_SIMP_TAC arith_ss [arithmeticTheory.ONE_LT_EXP]
      \\ `Num (-i) DIV 2 ** n < Num (-i)`
      by ASM_SIMP_TAC arith_ss [arithmeticTheory.DIV_LESS, ZERO_LT_TWOEXP]
      \\ `Num (-i) DIV 2 ** n + 1 <= Num (-i)` by DECIDE_TAC
      \\ `Num (-i) DIV 2 ** n + 1 < 2 ** dimindex (:'a)`
      by METIS_TAC [arithmeticTheory.LESS_EQ_TRANS,
                    arithmeticTheory.LESS_EQ_LESS_TRANS,
                    DIMINDEX_SUB1, TWOEXP_MONO]
      \\ ASM_SIMP_TAC arith_ss [BIT_SHIFT_THM4, bitTheory.NOT_BIT_GT_TWOEXP]
    ],
    SRW_TAC [ARITH_ss] [BIT_SHIFT_THM4]
    \\ FULL_SIMP_TAC std_ss [INT_MAX_def, wordsTheory.INT_MIN_def,
          intLib.ARITH_PROVE ``i <= &n - 1 = i < &n``]
    \\ `Num i < 2n ** (dimindex (:'a) - 1)` by intLib.ARITH_TAC
    \\ `dimindex (:'a) - 1 < i' + n` by DECIDE_TAC
    \\ `Num i < 2n ** (i' + n)` by METIS_TAC [TWOEXP_MONO, LESS_TRANS]
    \\ SRW_TAC [] [bitTheory.NOT_BIT_GT_TWOEXP]
  ]
);

(* ------------------------------------------------------------------------- *)

val INT_MIN_MONOTONIC = Q.store_thm("INT_MIN_MONOTONIC",
  `dimindex (:'a) <= dimindex (:'b) ==> INT_MIN (:'b) <= INT_MIN (:'a) : int`,
  SRW_TAC [] [INT_MIN_def, INT_MAX_def, wordsTheory.INT_MIN_def]
  \\ intLib.ARITH_TAC);

val INT_MAX_MONOTONIC = Q.store_thm("INT_MAX_MONOTONIC",
  `dimindex (:'a) <= dimindex (:'b) ==> INT_MAX (:'a) <= INT_MAX (:'b) : int`,
  SRW_TAC [] [INT_MAX_def, wordsTheory.INT_MIN_def,
              intLib.ARITH_PROVE ``x - 1 <= y - 1i = x <= y``]
  \\ intLib.ARITH_TAC);

val w2i_sw2sw_bounds = Q.store_thm("w2i_sw2sw_bounds",
  `!w : 'a word.
      INT_MIN (:'a) <= w2i (sw2sw w : 'b word) /\
      w2i (sw2sw w : 'b word) <= INT_MAX (:'a)`,
  STRIP_TAC \\ Cases_on `dimindex (:'b) <= dimindex (:'a)`
  THENL [
    IMP_RES_TAC INT_MIN_MONOTONIC
    \\ IMP_RES_TAC INT_MAX_MONOTONIC
    \\ Q.ISPEC_THEN `sw2sw w : 'b word` ASSUME_TAC w2i_le
    \\ Q.ISPEC_THEN `sw2sw w : 'b word` ASSUME_TAC w2i_ge
    \\ intLib.ARITH_TAC,
    FULL_SIMP_TAC std_ss [arithmeticTheory.NOT_LESS_EQUAL]
    \\ Cases_on_i2w `w : 'a word`
    \\ `dimindex (:'a) <= dimindex (:'b)` by DECIDE_TAC
    \\ IMP_RES_TAC INT_MIN_MONOTONIC
    \\ IMP_RES_TAC INT_MAX_MONOTONIC
    \\ SRW_TAC [intLib.INT_ARITH_ss] [sw2sw_i2w, w2i_i2w]
  ]);

val w2i_i2w_id = Q.store_thm("w2i_i2w_id",
  `!i. INT_MIN (:'a) <= i /\ i <= INT_MAX (:'a) /\
       dimindex (:'b) <= dimindex (:'a) ==>
       ((i = w2i (i2w i : 'b word)) =
        (i2w i = sw2sw (i2w i : 'b word) : 'a word))`,
  STRIP_TAC
  \\ Cases_on `INT_MIN (:'b) <= i /\ i <= INT_MAX (:'b)`
  \\ SRW_TAC [ARITH_ss] [sw2sw_i2w, w2i_i2w, GSYM w2i_11]
  \\ METIS_TAC [w2i_le, w2i_ge, w2i_sw2sw_bounds]);

val w2i_11_lift = Q.store_thm("w2i_11_lift",
  `!a:'a word b:'b word.
    dimindex (:'a) <= dimindex (:'c) /\ dimindex (:'b) <= dimindex (:'c) ==>
    ((w2i a = w2i b) = (sw2sw a = sw2sw b : 'c word))`,
  REPEAT STRIP_TAC
  \\ IMP_RES_TAC INT_MIN_MONOTONIC
  \\ IMP_RES_TAC INT_MAX_MONOTONIC
  \\ Cases_on_i2w `a:'a word`
  \\ Cases_on_i2w `b:'b word`
  \\ SRW_TAC [] [dimindex_dimword_le_iso, w2i_i2w, sw2sw_i2w]
  \\ `INT_MIN (:'c) <= i /\ i <= INT_MAX (:'c)` by intLib.ARITH_TAC
  \\ `INT_MIN (:'c) <= i' /\ i' <= INT_MAX (:'c)` by intLib.ARITH_TAC
  \\ SRW_TAC [] [GSYM w2i_11, w2i_i2w]);

val w2i_n2w_mod = Q.store_thm("w2i_n2w_mod",
  `!n m. n < dimword (:'a) /\ m <= dimindex (:'a) ==>
         (Num (w2i (n2w n : 'a word) % 2 ** m) = n MOD 2 ** m)`,
  REPEAT STRIP_TAC
  \\ `&(dimword (:'a) - n) = &dimword (:'a) - &n`
  by SRW_TAC [ARITH_ss] [integerTheory.INT_SUB]
  \\ `?q. dimword (:'a) = q * 2 ** m`
  by (IMP_RES_TAC LESS_EQUAL_ADD
      \\ Q.EXISTS_TAC `2n ** p`
      \\ ASM_SIMP_TAC arith_ss [dimword_def, EXP_ADD])
  \\ Cases_on `n < INT_MIN (:'a)`
  \\ FULL_SIMP_TAC arith_ss
       [NOT_LESS, w2i_n2w_neg, w2i_n2w_pos,
        simpLib.SIMP_PROVE (srw_ss()) [] ``2i ** n = &(2n ** n)``,
        integerTheory.NUM_OF_INT, int_arithTheory.INT_SUB_SUB3,
        integerTheory.INT_MOD_CALCULATE, integerTheory.INT_MOD_NEG_NUMERATOR]
  \\ `0i <> &(2n ** m)` by SRW_TAC [] []
  \\ ASM_SIMP_TAC arith_ss
       [Once (GSYM integerTheory.INT_MOD_SUB), integerTheory.INT_MOD_CALCULATE,
        arithmeticTheory.MOD_EQ_0, integerTheory.INT_SUB_RZERO,
        integerTheory.INT_MOD_ADD_MULTIPLES
        |> Q.INST [`q` |-> `1i`]
        |> REWRITE_RULE [integerTheory.INT_MUL_LID],
        integerTheory.NUM_OF_INT]);

val word_abs_w2i = Q.store_thm("word_abs_w2i",
  `!w. word_abs w = n2w (Num (ABS (w2i w)))`,
  STRIP_TAC \\ Cases_on_i2w `w : 'a word`
  \\ SRW_TAC [] [w2i_i2w, word_abs_def, WORD_LTi, word_0_w2i]
  \\ SRW_TAC [] [i2w_def, intLib.ARITH_PROVE ``~(i < 0) ==> (ABS i = i)``,
       intLib.ARITH_PROVE ``i < 0 ==> (ABS i = -i)``,
       wordsTheory.WORD_LITERAL_MULT]);

val word_abs_i2w = Q.store_thm("word_abs_i2w",
  `!i. INT_MIN (:'a) <= i /\ i <= INT_MAX (:'a) ==>
       (word_abs (i2w i) = n2w (Num (ABS i)) : 'a word)`,
  SRW_TAC [] [word_abs_w2i, w2i_i2w]);

(* ------------------------------------------------------------------------- *)

val _ = export_theory()
