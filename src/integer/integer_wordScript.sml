(* ========================================================================= *)
(* Theory of 2's complement representation of integers                       *)
(* ========================================================================= *)

open HolKernel boolLib Parse bossLib BasicProvers lcsymtacs

open wordsLib stringLib intLib arithmeticTheory
open bitTheory wordsTheory integerTheory

infix \\
val op \\ = op THEN;

val _ = new_theory "integer_word"

(* ------------------------------------------------------------------------- *)

val toString_def = Define`
   toString (i : int) =
      if i < 0 then
        "~" ++ num_to_dec_string (Num ~i)
      else
        num_to_dec_string (Num i)`;

val fromString_def = Define`
   (fromString (#"~"::t) = ~&(num_from_dec_string t)) /\
   (fromString (#"-"::t) = ~&(num_from_dec_string t)) /\
   (fromString s = &(num_from_dec_string s))`;

val i2w_def = Define`
  i2w (i : int) : 'a word =
    if i < 0 then -(n2w (Num(-i))) else n2w (Num i)`;

val w2i_def = Define`
  w2i w = if word_msb w then ~(int_of_num (w2n (word_2comp w)))
          else int_of_num (w2n w)`;

val UINT_MAX_def = Define`
  UINT_MAX (:'a) :int = &(dimword(:'a)) - 1`;

val INT_MAX_def = Define`
  INT_MAX (:'a) :int = &(words$INT_MIN(:'a)) - 1`;

val INT_MIN_def = Define`
  INT_MIN (:'a) = ~INT_MAX(:'a) - 1`;

val saturate_i2w_def = Define`
  saturate_i2w i : 'a word =
    if UINT_MAX (:'a) <= i then
      word_T
    else if i < 0 then
      0w
    else
      n2w (Num i)`;

val saturate_i2sw_def = Define`
  saturate_i2sw i : 'a word =
    if INT_MAX (:'a) <= i then
      word_H
    else if i <= INT_MIN (:'a) then
      word_L
    else
      i2w i`;

val saturate_sw2sw_def = Define`
  saturate_sw2sw (w: 'a word) = saturate_i2sw (w2i w)`;

val saturate_w2sw_def = Define`
  saturate_w2sw (w: 'a word) = saturate_i2sw (&w2n w)`;

val saturate_sw2w_def = Define`
  saturate_sw2w (w: 'a word) = saturate_i2w (w2i w)`;

val signed_saturate_add_def = Define`
  signed_saturate_add (a: 'a word) (b: 'a word) =
    saturate_i2sw (w2i a + w2i b) : 'a word`;

val signed_saturate_sub_def = Define`
  signed_saturate_sub (a: 'a word) (b: 'a word) =
    saturate_i2sw (w2i a - w2i b) : 'a word`;

(* ------------------------------------------------------------------------- *)

(*
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
*)

val ONE_LE_TWOEXP = save_thm("ONE_LE_TWOEXP", bitTheory.ONE_LE_TWOEXP);

val w2i_w2n_pos = Q.store_thm("w2i_w2n_pos",
  `!w n. ~word_msb w /\ w2i w < &n ==> w2n w < n`,
  SRW_TAC [] [w2i_def]);

val w2i_n2w_pos = store_thm(
  "w2i_n2w_pos",
  ``!n. n < INT_MIN (:'a) ==>
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
  ``!n. INT_MIN (:'a) <= n /\ n < dimword (:'a) ==>
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
  ``!w. i2w (w2i w) = w``,
  SRW_TAC [][i2w_def, w2i_def] THEN FULL_SIMP_TAC (srw_ss()) [])

val w2i_i2w = store_thm(
  "w2i_i2w",
  ``!i. INT_MIN (:'a) <= i /\ i <= INT_MAX (:'a)
      ==>
    (w2i (i2w i : 'a word) = i)``,
  STRIP_TAC THEN SIMP_TAC (srw_ss()) [INT_MIN_def, INT_MAX_def] THEN
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
  ``!i. word_msb (i2w i : 'a word) = &(INT_MIN(:'a)) <= i % &(dimword(:'a))``,
  STRIP_TAC THEN
  `dimword(:'a) = 2 * INT_MIN(:'a)` by ACCEPT_TAC dimword_IS_TWICE_INT_MIN THEN
  `0 < dimword(:'a)` by ACCEPT_TAC ZERO_LT_dimword THEN
  `1n <= INT_MIN(:'a) /\ 1 <= dimword(:'a)` by DECIDE_TAC THEN
  ASM_SIMP_TAC (srw_ss()) [i2w_def] THEN
  Cases_on `i < 0` THENL [
    `?n. (i = ~&n) /\ ~(n = 0)`
        by (Q.SPEC_THEN `i` STRIP_ASSUME_TAC INT_NUM_CASES THEN
            FULL_SIMP_TAC (srw_ss()) []) THEN
    `n MOD (2 * INT_MIN(:'a)) < 2 * INT_MIN(:'a)`
    by SRW_TAC [ARITH_ss][DIVISION] THEN
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
   Q.ISPEC_THEN t Tactic.FULL_STRUCT_CASES_TAC ranged_int_word_nchotomy

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
  \\ `?q. 0n < q /\ Num (-i) MOD (q * dimword (:'a)) < q * dimword (:'a) /\
      (dimword (:'b) = q * dimword (:'a))`
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

val INT_MIN = Q.store_thm("INT_MIN",
  `INT_MIN (:'a) = -&words$INT_MIN (:'a)`,
  SRW_TAC [] [INT_MIN_def, INT_MAX_def, wordsTheory.INT_MIN_def]);
val _ = export_rewrites ["INT_MIN"];

val INT_MAX = Q.store_thm("INT_MAX",
  `INT_MAX (:'a) = &words$INT_MAX (:'a)`,
  SRW_TAC [] [INT_MAX_def, wordsTheory.INT_MAX_def, int_arithTheory.INT_NUM_SUB]
  \\ FULL_SIMP_TAC arith_ss [wordsTheory.ZERO_LT_INT_MIN]);
val _ = export_rewrites ["INT_MAX"];

val UINT_MAX = Q.store_thm("UINT_MAX",
  `UINT_MAX (:'a) = &words$UINT_MAX (:'a)`,
  SRW_TAC [] [UINT_MAX_def, wordsTheory.UINT_MAX_def,
              int_arithTheory.INT_NUM_SUB]
  \\ ASSUME_TAC wordsTheory.ZERO_LT_dimword
  \\ DECIDE_TAC);
val _ = export_rewrites ["UINT_MAX"];

val INT_BOUND_ORDER = Q.store_thm("INT_BOUND_ORDER",
  `INT_MIN (:'a) < INT_MAX (:'a) : int /\
   INT_MAX (:'a) < UINT_MAX (:'a) : int /\
   UINT_MAX (:'a) < &dimword (:'a)`,
  SRW_TAC [ARITH_ss] [BOUND_ORDER]);

val INT_ZERO_LT_INT_MIN = Q.store_thm("INT_ZERO_LT_INT_MIN",
  `INT_MIN (:'a) < 0`,
  SRW_TAC [ARITH_ss] [ZERO_LT_INT_MIN]);
val _ = export_rewrites ["INT_ZERO_LT_INT_MIN"];

val INT_ZERO_LT_INT_MAX = Q.store_thm("INT_ZERO_LT_INT_MAX",
  `1 < dimindex(:'a) ==> 0i < INT_MAX (:'a)`,
  SRW_TAC [ARITH_ss] [ZERO_LT_INT_MAX]);

val INT_ZERO_LE_INT_MAX = Q.store_thm("INT_ZERO_LE_INT_MAX",
  `0i <= INT_MAX (:'a)`,
  SRW_TAC [ARITH_ss] [ZERO_LE_INT_MAX]);

val INT_ZERO_LT_UINT_MAX = Q.store_thm("INT_ZERO_LT_UINT_MAX",
  `0i < UINT_MAX (:'a)`,
  SRW_TAC [ARITH_ss] [ZERO_LT_UINT_MAX]);
val _ = export_rewrites ["INT_ZERO_LT_UINT_MAX"];

val w2i_1 = Q.store_thm("w2i_1",
  `w2i (1w:'a word) = if dimindex(:'a) = 1 then -1 else 1`,
  srw_tac [ARITH_ss]
      [wordsTheory.word_2comp_dimindex_1, w2i_def, word_msb_def,
       wordsTheory.word_index]
  \\ full_simp_tac (srw_ss()) [DECIDE ``0n < n /\ n <> 1 ==> ~(n <= 1)``]
);

val w2i_INT_MINw = Q.store_thm("w2i_INT_MINw",
  `w2i (INT_MINw: 'a word) = INT_MIN (:'a)`,
  SRW_TAC [ARITH_ss] [w2i_n2w_neg, word_L_def, INT_MIN_LT_DIMWORD,
     dimword_sub_int_min]);

val w2i_UINT_MAXw = Q.store_thm("w2i_UINT_MAXw",
  `w2i (UINT_MAXw: 'a word) = -1i`,
  SRW_TAC [ARITH_ss] [w2i_n2w_neg, word_T_def, BOUND_ORDER]
  \\ SRW_TAC [] [wordsTheory.UINT_MAX_def,
       DECIDE ``0n < n ==> (n - (n - 1) = 1)``]);

val w2i_INT_MAXw = Q.store_thm("w2i_INT_MAXw",
  `w2i (INT_MAXw: 'a word) = INT_MAX (:'a)`,
  RW_TAC arith_ss [w2i_n2w_pos, word_H_def, BOUND_ORDER]
  \\ SRW_TAC [] []);

val w2i_minus_1 = Theory.save_thm("w2i_minus_1",
  SIMP_RULE (srw_ss()) [] w2i_UINT_MAXw);

val w2i_lt_0 = Q.store_thm("w2i_lt_0",
  `!w: 'a word. w2i w < 0 = w < 0w`,
  STRIP_TAC \\ Cases_on_i2w `w: 'a word`
  \\ SRW_TAC [] [w2i_i2w, word_0_w2i, WORD_LTi]);

val w2i_neg = Q.store_thm("w2i_neg",
  `!w:'a word. 1 < dimindex(:'a) /\ w <> INT_MINw ==> (w2i (-w) = -w2i w)`,
  SRW_TAC [] [w2i_def]
  \\ IMP_RES_TAC TWO_COMP_POS
  \\ IMP_RES_TAC TWO_COMP_NEG
  \\ NTAC 2 (POP_ASSUM MP_TAC)
  \\ SRW_TAC [ARITH_ss] []
  \\ FULL_SIMP_TAC (srw_ss()) []);

val i2w_0 = Q.store_thm("i2w_0",
  `i2w 0 = 0w`,
  SRW_TAC [] [i2w_def]);

val i2w_minus_1 = Q.store_thm("i2w_minus_1",
  `i2w (-1) = -1w`,
  SRW_TAC [] [i2w_def]);

val i2w_INT_MIN = Q.store_thm("i2w_INT_MIN",
  `i2w (INT_MIN (:'a)) = INT_MINw : 'a word`,
  `INT_MIN (:'a) <= INT_MAX (:'a) : int`
  by SRW_TAC [intLib.INT_ARITH_ss] [INT_BOUND_ORDER]
  \\ RW_TAC (std_ss++intLib.INT_ARITH_ss) [GSYM w2i_11, w2i_INT_MINw, w2i_i2w]);

val i2w_INT_MAX = Q.store_thm("i2w_INT_MAX",
  `i2w (INT_MAX (:'a)) = INT_MAXw : 'a word`,
  `INT_MIN (:'a) <= INT_MAX (:'a) : int`
  by SRW_TAC [intLib.INT_ARITH_ss] [INT_BOUND_ORDER]
  \\ RW_TAC (std_ss++intLib.INT_ARITH_ss) [GSYM w2i_11, w2i_INT_MAXw, w2i_i2w]);

val i2w_UINT_MAX = Q.store_thm("i2w_UINT_MAX",
  `i2w (UINT_MAX (:'a)) = UINT_MAXw : 'a word`,
  rw_tac (std_ss++intLib.INT_ARITH_ss) [GSYM w2i_11, w2i_UINT_MAXw, i2w_def]
  \\ full_simp_tac std_ss [INT_ZERO_LT_UINT_MAX,
       intLib.ARITH_PROVE ``0i < n ==> ~(n < 0i)``]
  \\ fsrw_tac [] [GSYM wordsTheory.word_T_def, w2i_minus_1]
);

val saturate_i2w_0 = Q.store_thm("saturate_i2w_0",
  `saturate_i2w 0 = 0w`,
  SRW_TAC [ARITH_ss] [saturate_i2w_def, wordsTheory.ZERO_LT_UINT_MAX]);

val saturate_i2sw_0 = Q.store_thm("saturate_i2sw_0",
  `saturate_i2sw 0 = 0w`,
  SRW_TAC [ARITH_ss] [i2w_0, saturate_i2sw_def]
  \\ FULL_SIMP_TAC arith_ss
       [wordsTheory.ZERO_LT_INT_MIN, DECIDE ``0n < n ==> n <> 0``]
  \\ Cases_on `1 < dimindex(:'a)`
  \\ FULL_SIMP_TAC arith_ss
       [wordsTheory.ZERO_LT_INT_MAX, DECIDE ``0n < n ==> n <> 0``]
  \\ `dimindex (:'a) = 1`
  by SRW_TAC [] [DECIDE ``0n < n /\ ~(1 < n) ==> (n = 1)``]
  \\ SRW_TAC [] [word_L_def, wordsTheory.INT_MIN_def]);

(* ------------------------------------------------------------------------- *)

val saturate_w2sw = Q.store_thm("saturate_w2sw",
  `!w: 'a word.
    saturate_w2sw w : 'b word =
      if dimindex(:'b) <= dimindex(:'a) /\ w2w (word_H: 'b word) <=+ w then
        word_H
      else
        w2w w`,
  Cases
  \\ SIMP_TAC (srw_ss()++ARITH_ss) [word_H_def, w2w_def, word_ls_n2w,
        wordsTheory.INT_MAX_def, wordsTheory.INT_MIN_LT_DIMWORD,
        INT_MAX_def, INT_MIN_def, saturate_w2sw_def, saturate_i2sw_def, i2w_def]
  \\ SIMP_TAC (std_ss++INT_ARITH_ss) []
  \\ `INT_MIN (:'b) < dimword (:'b)`
  by METIS_TAC [arithmeticTheory.LESS_EQ_LESS_TRANS, BOUND_ORDER]
  \\ Cases_on `dimindex (:'b) <= dimindex (:'a)`
  \\ IMP_RES_TAC wordsTheory.dimindex_dimword_le_iso
  \\ ASM_SIMP_TAC (srw_ss()++ARITH_ss)
        [ARITH_PROVE ``&m - 1i <= &n = m <= n + 1n``]
  \\ Cases_on `n = INT_MIN (:'b) - 1`
  \\ ASM_SIMP_TAC arith_ss []
  \\ `~(INT_MIN (:'b) <= n + 1)`
  by (
    `dimword(:'a) <= INT_MIN (:'b)`
    by SRW_TAC [ARITH_ss] [dimword_def, wordsTheory.INT_MIN_def]
    \\ ASM_SIMP_TAC arith_ss [NOT_LESS_EQUAL, wordsTheory.ZERO_LT_INT_MIN]
  )
  \\ ASM_REWRITE_TAC []
);

val saturate_i2sw = Q.store_thm("saturate_i2sw",
  `!i. saturate_i2w i = if i < 0 then 0w else saturate_n2w (Num i)`,
  Cases
  \\ ASM_SIMP_TAC (arith_ss++INT_ARITH_ss)
       [integerTheory.INT_LE, integerTheory.NUM_OF_INT,
        wordsTheory.ZERO_LT_dimword, ZERO_LT_UINT_MAX,
        saturate_i2w_def, saturate_n2w_def, UINT_MAX,
        DECIDE ``0n < n ==> n <> 0``]
  \\ ASM_SIMP_TAC std_ss
       [intLib.ARITH_PROVE ``n <> 0n ==> -&n < 0``,
        intLib.ARITH_PROVE ``n <> 0n ==> ~(&m <= -&n)``]
  \\ Cases_on `n = UINT_MAX (:'a)`
  \\ ASM_SIMP_TAC arith_ss [BOUND_ORDER, word_T_def]
  \\ `UINT_MAX (:'a) <= n /\ n <> UINT_MAX (:'a) = dimword (:'a) <= n`
  by SIMP_TAC (srw_ss()) [wordsTheory.UINT_MAX_def,
       DECIDE ``0n < m ==> (m <= 1 + n /\ n <> m - 1 = m <= n)``]
  \\ METIS_TAC []);

val saturate_sw2w = Q.store_thm("saturate_sw2w",
  `!w: 'a word.
    saturate_sw2w w : 'b word =
      if w < 0w then
        0w
      else
        saturate_w2w w`,
  STRIP_TAC
  \\ SIMP_TAC arith_ss
       [w2i_lt_0, saturate_w2w, saturate_sw2w_def, saturate_i2sw]
  \\ Cases_on `w < 0w : 'a word`
  \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `w`
  \\ FULL_SIMP_TAC arith_ss [w2i_n2w_pos, wordsTheory.w2n_n2w, saturate_n2w_def,
       WORD_NOT_LESS, wordsTheory.WORD_ZERO_LE, GSYM MOD_DIMINDEX, w2w_n2w,
       integerTheory.NUM_OF_INT]
  \\ Cases_on `dimindex (:'b) <= dimindex (:'a)`
  \\ ASM_SIMP_TAC arith_ss []
  THENL [
    `UINT_MAX (:'b) < dimword (:'b)` by METIS_TAC [BOUND_ORDER]
    \\ IMP_RES_TAC wordsTheory.dimindex_dimword_le_iso
    \\ `UINT_MAX (:'b) < dimword (:'a)` by DECIDE_TAC
    \\ ASM_SIMP_TAC arith_ss
         [w2w_n2w, word_T_def, word_ls_n2w, GSYM MOD_DIMINDEX]
    \\ Cases_on `n < UINT_MAX (:'b)`
    \\ FULL_SIMP_TAC arith_ss [NOT_LESS]
    \\ Cases_on `n = UINT_MAX (:'b)`
    \\ ASM_SIMP_TAC arith_ss []
    \\ `dimword (:'b) <= n` by FULL_SIMP_TAC arith_ss [wordsTheory.UINT_MAX_def]
    \\ ASM_REWRITE_TAC [],
    FULL_SIMP_TAC arith_ss [NOT_LESS_EQUAL, wordsTheory.dimindex_dimword_lt_iso]
  ]
);

val saturate_sw2sw = Q.store_thm("saturate_sw2sw",
  `!w: 'a word.
    saturate_sw2sw w : 'b word =
      if dimindex(:'a) <= dimindex(:'b) then
        sw2sw w
      else if sw2sw (word_H: 'b word) <= w then
        word_H
      else if w <= sw2sw (word_L: 'b word) then
        word_L
      else
        w2w w`,
  STRIP_TAC \\ Cases_on_i2w `w:'a word`
  \\ ASM_SIMP_TAC std_ss [saturate_sw2sw_def, saturate_i2sw_def, w2i_i2w]
  \\ Cases_on `dimindex (:'a) <= dimindex (:'b)`
  \\ IMP_RES_TAC INT_MAX_MONOTONIC
  \\ IMP_RES_TAC INT_MIN_MONOTONIC
  \\ ASM_SIMP_TAC arith_ss [sw2sw_i2w, w2w_i2w]
  THENL [
    SRW_TAC [] [word_H_def, word_L_def]
    THENL [
      `i <= INT_MAX (:'b)` by intLib.ARITH_TAC
      \\ `i = INT_MAX (:'b)` by FULL_SIMP_TAC (srw_ss()++INT_ARITH_ss) []
      \\ ASM_SIMP_TAC (srw_ss()) [i2w_def],
      `INT_MIN (:'b) <= i` by intLib.ARITH_TAC
      \\ `i = INT_MIN (:'b)` by FULL_SIMP_TAC (srw_ss()++INT_ARITH_ss) []
      \\ ASM_SIMP_TAC (srw_ss()) [i2w_def, DECIDE ``0n < n ==> (n <> 0)``]
      \\ SIMP_TAC std_ss [GSYM word_L_def, wordsTheory.WORD_NEG_L]
    ],
    FULL_SIMP_TAC std_ss [NOT_LESS_EQUAL]
    \\ `n2w (INT_MAX (:'b)) : 'b word = i2w (&INT_MAX (:'b))`
    by SRW_TAC [] [i2w_def]
    \\ `n2w (INT_MIN (:'b)) : 'b word = i2w (-&INT_MIN (:'b))`
    by (SRW_TAC [ARITH_ss] [i2w_def]
        THEN1 SIMP_TAC std_ss [GSYM word_L_def, wordsTheory.WORD_NEG_L]
        \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ `INT_MIN (:'b) <= &(INT_MAX (:'b) : num) /\
        &(INT_MAX (:'b) : num) <= INT_MAX (:'b)`
    by SRW_TAC [INT_ARITH_ss] []
    \\ `INT_MIN (:'b) <= -&(INT_MIN (:'b) : num) /\
        -&(INT_MIN (:'b) : num) <= INT_MAX (:'b)`
    by SRW_TAC [INT_ARITH_ss] []
    \\ `INT_MAX (:'b) < INT_MAX (:'a) : int /\
        INT_MIN (:'a) < INT_MIN (:'b) : int`
    by SRW_TAC [] [GSYM dimindex_int_max_lt_iso, GSYM dimindex_int_min_lt_iso]
    \\ `INT_MIN (:'a) <= &(INT_MAX (:'b) : num) /\
        &(INT_MAX (:'b) : num) <= INT_MAX (:'a)`
    by intLib.ARITH_TAC
    \\ `INT_MIN (:'a) <= -&(INT_MIN (:'b) : num) /\
        -&(INT_MIN (:'b) : num) <= INT_MAX (:'a)`
    by intLib.ARITH_TAC
    \\ ASM_SIMP_TAC arith_ss
         [word_H_def, word_L_def, sw2sw_i2w, WORD_LEi, w2i_i2w]
    \\ SIMP_TAC (srw_ss()) []
  ]
);

(* ------------------------------------------------------------------------- *)

val signed_saturate_sub = Q.store_thm("signed_saturate_sub",
  `!a b:'a word.
     signed_saturate_sub a b =
       if b = INT_MINw then
         if 0w <= a then
           INT_MAXw
         else
           a + INT_MINw
       else if dimindex(:'a) = 1 then
         a && ~b
       else
         signed_saturate_add a (-b)`,
  srw_tac [] [signed_saturate_add_def, signed_saturate_sub_def]
  \\ rule_assum_tac
       (SIMP_RULE (srw_ss()) [GSYM w2i_11, word_0_w2i, WORD_LEi, w2i_INT_MINw])
  THENL [
    (* Case 1 *)
    Cases_on_i2w `a:'a word`
    \\ srw_tac [ARITH_ss] [w2i_i2w, saturate_i2sw_def, w2i_INT_MINw]
    \\ full_simp_tac (srw_ss())
         [w2i_i2w, integerTheory.INT_NOT_LE, wordsTheory.INT_MAX_def,
          int_arithTheory.INT_NUM_SUB, DECIDE ``0n < n ==> ~(n < 1)``,
          intLib.ARITH_PROVE ``i + &n < &n - 1 = i < -1i``,
          wordsTheory.ZERO_LT_INT_MIN,
          intLib.ARITH_PROVE ``i < -1i ==> ~(0 <= i)``,
          intLib.ARITH_PROVE ``0n < n /\ i + &n <= -&n ==> ~(-&n <= i : int)``],
    (* Case 2 *)
    Cases_on_i2w `a:'a word`
    \\ srw_tac [ARITH_ss] [w2i_i2w, saturate_i2sw_def, w2i_INT_MINw]
    \\ full_simp_tac (srw_ss())
          [w2i_i2w, integerTheory.INT_NOT_LE, wordsTheory.INT_MAX_def,
           int_arithTheory.INT_NUM_SUB, DECIDE ``0n < n ==> ~(n < 1)``]
    THENL [
      `i = -1i` by intLib.ARITH_TAC \\ asm_rewrite_tac [i2w_minus_1],
      spose_not_then (K ALL_TAC) \\ intLib.ARITH_TAC,
      srw_tac [] [GSYM word_i2w_add,
            wordsLib.WORD_ARITH_PROVE ``(a + b = c + a) = (b = c : 'a word)``]
      \\ once_rewrite_tac [GSYM wordsTheory.WORD_NEG_L]
      \\ rewrite_tac
           [wordsLib.WORD_ARITH_PROVE ``(a = -b : 'a word) = (-1w * a = b)``,
            MULT_MINUS_ONE, GSYM INT_MIN, i2w_INT_MIN]
    ],
    (* Case 3 *)
    imp_res_tac dimindex_1_cases
    \\ pop_assum (fn th => assume_tac (Q.SPEC `a:'a word` th) \\
                           assume_tac (Q.SPEC `b:'a word` th))
    \\ full_simp_tac (srw_ss())
         [saturate_i2sw_0, word_0_w2i, w2i_1, w2i_minus_1]
    \\ srw_tac []
         [saturate_i2sw_def, word_L_def, wordsTheory.INT_MIN_def, i2w_def]
    \\ pop_assum mp_tac
    \\ srw_tac [] [wordsTheory.INT_MAX_def, wordsTheory.INT_MIN_def],
    (* Case 4 *)
    `1 < dimindex(:'a)` by srw_tac [] [DECIDE ``0n < n /\ n <> 1 ==> (1 < n)``]
    \\ asm_simp_tac std_ss [GSYM integerTheory.int_sub,
         SIMP_RULE (srw_ss()) [GSYM w2i_11, w2i_INT_MINw] w2i_neg]
  ]
);

val add_min_overflow = Q.prove(
  `!i j.
     i + j < INT_MIN (:'a) /\
     INT_MIN (:'a) <= i /\ i < 0 /\
     INT_MIN (:'a) <= j /\ j <= INT_MAX (:'a) ==>
     0 <= w2i (i2w (i + j) : 'a word)`,
  srw_tac [] [w2i_def, WORD_MSB_INT_MIN_LS]
  \\ spose_not_then kall_tac
  \\ `i + j < 0` by intLib.ARITH_TAC
  \\ `2i * -&INT_MIN (:'a) <= i + j` by intLib.ARITH_TAC
  \\ rule_assum_tac
       (ONCE_REWRITE_RULE [intLib.ARITH_PROVE ``-x <= y = -y <= x : int``] o
        REWRITE_RULE [GSYM dimword_IS_TWICE_INT_MIN,
          intLib.ARITH_PROVE ``2i * -&n = -&(2n * n)``])
  \\ `Num (-(i + j)) <= dimword (:'a)` by intLib.ARITH_TAC
  \\ fsrw_tac [ARITH_ss]
       [INT_MIN_LT_DIMWORD, i2w_def, word_2comp_n2w, word_L_def, word_ls_n2w]
  \\ Cases_on `Num (-(i + j)) = dimword (:'a)`
  >- fsrw_tac [ARITH_ss] [DECIDE ``0 < n ==> n <> 0n``]
  \\ `Num (-(i + j)) < dimword (:'a)` by DECIDE_TAC
  \\ `INT_MIN (:'a) < Num (-(i + j))` by intLib.ARITH_TAC
  \\ fsrw_tac [ARITH_ss] [dimword_IS_TWICE_INT_MIN]);

val add_max_overflow = Q.prove(
  `!i j.
     INT_MAX (:'a) < i + j /\
     0 <= i /\ i <= INT_MAX (:'a) /\
     INT_MIN (:'a) <= j /\ j <= INT_MAX (:'a) ==>
     w2i (i2w (i + j) : 'a word) < 0`,
  srw_tac [] [] \\ srw_tac [] [w2i_def, WORD_MSB_INT_MIN_LS]
  >| [
    spose_not_then strip_assume_tac
    \\ fsrw_tac []
         [REWRITE_RULE [GSYM wordsTheory.WORD_NOT_LOWER_EQUAL]
            wordsTheory.ZERO_LO_INT_MIN],
    pop_assum mp_tac \\ rewrite_tac []
    \\ `~(i + j < 0)` by intLib.ARITH_TAC
    \\ `i + j <= 2 * &INT_MAX (:'a)` by intLib.ARITH_TAC
    \\ `2 * &INT_MAX (:'a) < &dimword (:'a)`
    by srw_tac [] [dimword_IS_TWICE_INT_MIN, wordsTheory.INT_MAX_def]
    \\ `Num (i + j) < dimword (:'a)` by intLib.ARITH_TAC
    \\ fsrw_tac [ARITH_ss] [wordsTheory.INT_MIN_LT_DIMWORD,
         i2w_def, word_L_def, wordsTheory.word_ls_n2w]
    \\ fsrw_tac [ARITH_ss]
           [wordsTheory.INT_MAX_def,
            intLib.ARITH_PROVE ``~(y < 0i) ==> (&x < y = x < Num y)``]
  ]
);

val srw_add_min_overflow = SIMP_RULE (srw_ss()) [] add_min_overflow;
val srw_add_max_overflow = SIMP_RULE (srw_ss()) [] add_max_overflow;

val signed_saturate_add = Q.store_thm("signed_saturate_add",
  `!a b:'a word.
     signed_saturate_add a b =
       let sum = a + b and msba = word_msb a in
         if (msba = word_msb b) /\ (msba <> word_msb sum) then
           if msba then INT_MINw else INT_MAXw
         else
           sum`,
  ntac 2 strip_tac
  \\ Cases_on_i2w `a : 'a word`
  \\ Cases_on_i2w `b : 'a word`
  \\ fsrw_tac [boolSimps.LET_ss] [w2i_i2w, word_i2w_add,
       wordsTheory.word_msb_neg, signed_saturate_add_def,
       integerTheory.INT_NOT_LT, WORD_LEi, WORD_LTi, word_0_w2i]
  \\ srw_tac [] []
  >| [
    (* Case 1 *)
    `i < 0i` by metis_tac []
    \\ `i + i' < INT_MAX (:'a)`
    by srw_tac [intLib.INT_ARITH_ss] [INT_ZERO_LE_INT_MAX]
    \\ `i + i' <= INT_MAX (:'a)` by intLib.ARITH_TAC
    \\ `i + i' < INT_MIN (:'a)`
    by (spose_not_then
            (assume_tac o SIMP_RULE std_ss [integerTheory.INT_NOT_LT])
       \\ full_simp_tac std_ss [w2i_i2w]
       \\ intLib.ARITH_TAC)
    \\ fsrw_tac [intLib.INT_ARITH_ss] [saturate_i2sw_def],
    (* Case 2 *)
    `~(i < 0i)` by metis_tac []
    \\ fsrw_tac [intLib.INT_ARITH_ss] [integerTheory.INT_NOT_LT]
    \\ `INT_MIN (:'a) <= i + i'` by srw_tac [intLib.INT_ARITH_ss] []
    \\ `INT_MAX (:'a) < i + i'`
    by (spose_not_then
            (assume_tac o SIMP_RULE std_ss [integerTheory.INT_NOT_LT])
       \\ full_simp_tac std_ss [w2i_i2w]
       \\ intLib.ARITH_TAC)
    \\ asm_simp_tac std_ss [integerTheory.INT_LT_IMP_LE, saturate_i2sw_def]
    \\ srw_tac [] [],
    (* Case 3 *)
    `~(INT_MAX (:'a) < i + i') /\ ~(i + i' < INT_MIN (:'a))`
    by (fsrw_tac [intLib.INT_ARITH_ss] [integerTheory.INT_NOT_LT]
        \\ Cases_on `i < 0i`
        \\ fsrw_tac [intLib.INT_ARITH_ss] [integerTheory.INT_NOT_LT]
        \\ metis_tac [srw_add_min_overflow, srw_add_max_overflow,
             integerTheory.INT_NOT_LT, integerTheory.INT_NOT_LE])
    \\ simp_tac std_ss [saturate_i2sw_def]
    \\ Cases_on `INT_MAX (:'a) = i + i'`
    \\ full_simp_tac std_ss [integerTheory.INT_LE_REFL, GSYM i2w_INT_MAX]
    \\ `~(INT_MAX (:'a) <= i + i')` by intLib.ARITH_TAC
    \\ asm_rewrite_tac []
    \\ Cases_on `i + i' = INT_MIN (:'a)`
    \\ full_simp_tac std_ss [integerTheory.INT_LE_REFL, GSYM i2w_INT_MIN]
    \\ `~(i + i' <= INT_MIN (:'a))` by intLib.ARITH_TAC
    \\ asm_rewrite_tac []
  ]
);

(* ------------------------------------------------------------------------- *)

val different_sign_then_no_overflow = Q.store_thm(
  "different_sign_then_no_overflow",
  `!x y. word_msb x <> word_msb y ==> (w2i (x + y) = w2i x + w2i y)`,
  rw [GSYM word_add_i2w, wordsTheory.word_msb_neg, GSYM w2i_lt_0]
  \\ match_mp_tac w2i_i2w
  \\ qspec_then `x` assume_tac w2i_ge
  \\ qspec_then `x` assume_tac w2i_le
  \\ qspec_then `y` assume_tac w2i_ge
  \\ qspec_then `y` assume_tac w2i_le
  \\ intLib.ARITH_TAC);

val w2i_i2w_pos = Q.store_thm("w2i_i2w_pos",
   `!n. n <= INT_MAX (:'a) ==> (w2i (i2w (&n) : 'a word) = &n)`,
   ntac 2 strip_tac \\ match_mp_tac w2i_i2w
   \\ fsrw_tac [intLib.INT_ARITH_ss] []);

val w2i_i2w_neg = Q.store_thm("w2i_i2w_neg",
   `!n. n <= INT_MIN (:'a) ==> (w2i (i2w (-&n) : 'a word) = -&n)`,
   ntac 2 strip_tac \\ match_mp_tac w2i_i2w
   \\ fsrw_tac [intLib.INT_ARITH_ss] []);

val lem_pos = Q.prove(
   `!n:num. n <= INT_MAX (:'a) ==> ~(INT_MIN (:'a) <= n)`,
   lrw [wordsTheory.BOUND_ORDER, arithmeticTheory.NOT_LESS_EQUAL]);

val lem_neg = Q.prove(
   `!n. n <> 0n /\ n <= INT_MIN (:'a) ==>
        &INT_MIN (:'a) <= (&dimword (:'a) - &n) % &dimword (:'a)`,
   REPEAT strip_tac
   \\ `&n:int < &dimword (:'a)` by lrw [wordsTheory.BOUND_ORDER]
   \\ `0i <= &dimword (:'a) - &n /\ &dimword (:'a) - &n < &dimword (:'a) : int`
   by intLib.ARITH_TAC
   \\ lfs [integerTheory.INT_LESS_MOD, integerTheory.INT_SUB,
           wordsTheory.dimword_IS_TWICE_INT_MIN]);

val lem = Q.prove(
  `!n. &INT_MIN (:'a) <= &dimword (:'a) - &n : int = n <= INT_MIN (:'a)`,
  srw_tac [intLib.INT_ARITH_ss]
    [intLib.ARITH_PROVE ``a <= b - c = c <= b - a : int``,
     intLib.ARITH_PROVE ``&(2n * a) - &a = &a : int``,
     wordsTheory.dimword_IS_TWICE_INT_MIN]);

val overflow = Q.store_thm("overflow",
  `!x y. w2i (x + y) <> w2i x + w2i y =
         ((word_msb x = word_msb y) /\ word_msb x <> word_msb (x + y))`,
  ntac 2 strip_tac
  \\ Cases_on `word_msb x = word_msb y`
  \\ simp [different_sign_then_no_overflow]
  \\ Cases_on_i2w `x`
  \\ Cases_on_i2w `y`
  \\ fs [w2i_i2w, word_i2w_add, word_msb_i2w]
  \\ `i < &dimword (:'a) /\ i' <  &dimword (:'a)`
  by (ASSUME_TAC wordsTheory.INT_MAX_LT_DIMWORD \\ intLib.ARITH_TAC)
  \\ `&dimword (:'a) <> 0i /\ INT_MIN (:'a) <> 0n`
  by lfs [DECIDE ``0 < n ==> n <> 0n``]
  \\ Cases_on `i`
  \\ Cases_on `i'`
  \\ fsrw_tac [intLib.INT_ARITH_ss]
       [integerTheory.INT_MOD_NEG_NUMERATOR, integerTheory.INT_LESS_MOD,
        i2w_0, word_0_w2i, arithmeticTheory.NOT_LESS_EQUAL,
        w2i_i2w_pos, w2i_i2w_neg, lem_pos, lem_neg]
  \\ `&n + &n' <> 0i` by intLib.ARITH_TAC
  >- (`&n + &n' < &dimword (:'a) : int`
     by (lrw [integerTheory.INT_ADD, wordsTheory.dimword_IS_TWICE_INT_MIN]
         \\ metis_tac [wordsTheory.BOUND_ORDER,
              DECIDE ``a <= n /\ b <= n /\ n < m ==> a + b < 2n * m``])
     \\ lrw [integerTheory.INT_LESS_MOD, integerTheory.INT_ADD,
             arithmeticTheory.NOT_LESS_EQUAL]
     \\ Cases_on `n + n' <= INT_MAX (:'a)` \\ simp [w2i_i2w_pos]
     >- metis_tac [arithmeticTheory.LESS_EQ_LESS_TRANS, wordsTheory.BOUND_ORDER]
     \\ `INT_MIN (:'a) <= n + n'`
     by lfs [arithmeticTheory.NOT_LESS_EQUAL, wordsTheory.INT_MAX_def]
     \\ simp [i2w_def]
     \\ lfs [integerTheory.INT_ADD, w2i_def, wordsTheory.word_msb_n2w_numeric])
  \\ Cases_on `n + n' = dimword (:'a)`
  \\ simp [integerTheory.INT_ADD_CALCULATE, integerTheory.INT_MOD_NEG_NUMERATOR]
  >- lrw [word_0_w2i, i2w_def, n2w_dimword]
  \\ `&dimword (:'a) - &(n + n') < &dimword (:'a) : int` by intLib.ARITH_TAC
  \\ `&(n + n') < &dimword (:'a) : int`
  by lrw [integerTheory.INT_ADD, wordsTheory.dimword_IS_TWICE_INT_MIN]
  \\ `0i <= &dimword (:'a) - &(n + n')` by intLib.ARITH_TAC
  \\ lrw [integerTheory.INT_ADD_CALCULATE, integerTheory.INT_MOD_NEG_NUMERATOR,
          integerTheory.INT_LESS_MOD, lem]
  \\ Cases_on `n + n' <= INT_MIN (:'a)`
  \\ simp [w2i_i2w_neg]
  \\ `INT_MIN (:'a) < n + n'` by intLib.ARITH_TAC
  \\ lfs [i2w_def, wordsTheory.word_2comp_n2w]
  \\ imp_res_tac arithmeticTheory.LESS_ADD
  \\ `p' < INT_MIN (:'a)` by lrw [wordsTheory.dimword_IS_TWICE_INT_MIN]
  \\ qpat_assum `a + b = dimword(:'a)` (SUBST1_TAC o SYM)
  \\ lrw [w2i_def, wordsTheory.word_msb_n2w_numeric]);

(* ------------------------------------------------------------------------- *)

val _ = export_theory()
