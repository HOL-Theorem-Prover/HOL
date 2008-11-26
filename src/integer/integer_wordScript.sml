open HolKernel boolLib Parse bossLib BasicProvers

open wordsTheory integerTheory intLib arithmeticTheory

(* theory of 2's complement representation of integers *)

val _ = new_theory "integer_word"

val i2w_def = Define`
  i2w (i : int) : 'a word =
    if i < 0 then $- (n2w (Num ~i)) else n2w (Num i)
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
               Once (DECIDE ``w2n ($- b) + a = a + w2n ($- b)``)]
        THEN Cases_on `~BIT (dimindex (:'a)) (w2n a + w2n ($- b))`
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

(* ----------------------------------------------------------------------- *)

(* Emit integer operations as ML *)

val neg_int_of_num_def = Define `neg_int_of_num n = ~ int_of_num (n + 1)`;
val i2w_itself_def = Define `i2w_itself(i,(:'a)) = i2w i : 'a word`;

val i2w_itself = REWRITE_RULE [i2w_def] i2w_itself_def;

val emit_rule = SIMP_RULE std_ss [numeralTheory.iZ, NUMERAL_DEF];

fun emit_conv l1 l2 = LIST_CONJ
 (map (GEN_ALL o (SIMP_CONV (srw_ss()) (neg_int_of_num_def::l1)
    THENC REWRITE_CONV [GSYM neg_int_of_num_def])) l2);

val lem1 = DECIDE ``~(n + 1n <= m) ==> (n + 1 - m = (n - m) + 1)``;
val lem2 = DECIDE ``m + 1n + (n + 1) = m + n + 1 + 1``;

val INT_NEG_EMIT = Q.prove(
  `(!n. ~ (int_of_num n) =
         if n = 0 then int_of_num 0 else neg_int_of_num (n - 1)) /\
   (!n. ~ (neg_int_of_num n) = int_of_num (n + 1))`,
  SRW_TAC [ARITH_ss] [neg_int_of_num_def]);

val INT_ADD_EMIT = emit_conv [emit_rule INT_ADD_REDUCE, lem1, lem2]
   [``int_of_num m + int_of_num n``,
    ``neg_int_of_num m + int_of_num n``,
    ``int_of_num m + neg_int_of_num n``,
    ``neg_int_of_num m + neg_int_of_num n``];

val INT_SUB_EMIT = emit_conv [emit_rule INT_SUB_REDUCE]
   [``int_of_num m - int_of_num n``,
    ``neg_int_of_num m - int_of_num n``,
    ``int_of_num m - neg_int_of_num n``,
    ``neg_int_of_num m - neg_int_of_num n``];

val INT_MUL_EMIT = emit_conv [emit_rule INT_MUL_REDUCE]
   [``int_of_num m * int_of_num n``,
    ``neg_int_of_num m * int_of_num n``,
    ``int_of_num m * neg_int_of_num n``,
    ``neg_int_of_num m * neg_int_of_num n``];

val INT_LT_EMIT = emit_conv [emit_rule INT_LT_CALCULATE]
   [``int_of_num m < int_of_num n``,
    ``neg_int_of_num m < int_of_num n``,
    ``int_of_num m < neg_int_of_num n``,
    ``neg_int_of_num m < neg_int_of_num n``];

val INT_NEG_EXP = Q.prove(
  `!m n.
      neg_int_of_num m ** n =
        if EVEN n then
          int_of_num ((m + 1) ** n)
        else
          ~int_of_num ((m + 1) ** n)`,
  SRW_TAC [] [neg_int_of_num_def, INT_EXP_NEG]
    THEN FULL_SIMP_TAC std_ss [INT_EXP_NEG, GSYM ODD_EVEN]);

val INT_EXP_EMIT = CONJ INT_EXP INT_NEG_EXP;

val INT_Num_EMIT = Q.prove(
  `(!n. Num (int_of_num n) = n) /\
   (!n. Num (neg_int_of_num n) =
     FAIL $Num ^(mk_var("negative",bool)) (neg_int_of_num n))`,
  SRW_TAC [] [combinTheory.FAIL_THM]);

val INT_DIV_EMIT = Q.prove(
  `!i j. i / j =
      if j = 0 then FAIL $/ ^(mk_var("zero denominator",bool)) i j
      else
        ^((rhs o snd o dest_imp o snd o strip_forall o concl) int_div)`,
  SRW_TAC [] [combinTheory.FAIL_THM, int_div]);

val INT_MOD_EMIT = Q.prove(
  `!i j. i % j =
      if j = 0 then FAIL $% ^(mk_var("zero denominator",bool)) i j
      else
        ^((rhs o snd o dest_imp o snd o strip_forall o concl) int_mod)`,
  SRW_TAC [] [combinTheory.FAIL_THM, int_mod]);

val INT_QUOTE_EMIT = Q.prove(
  `!i j. i quot j =
      if j = 0 then FAIL $quot ^(mk_var("zero denominator",bool)) i j
      else
        ^((rhs o snd o dest_imp o snd o strip_forall o concl) int_quot)`,
  SRW_TAC [] [combinTheory.FAIL_THM, int_quot]);

val INT_REM_EMIT = Q.prove(
  `!i j. i rem j =
      if j = 0 then FAIL $rem ^(mk_var("zero denominator",bool)) i j
      else
        ^((rhs o snd o dest_imp o snd o strip_forall o concl) int_rem)`,
  SRW_TAC [] [combinTheory.FAIL_THM, int_rem]);

local
  open EmitML
  val _ = type_pp.pp_num_types := false;
  val _ = type_pp.pp_array_types := false;
  val _ = temp_clear_overloads_on "&";
  val _ = temp_overload_on("int_of_num", ``integer$int_of_num``);
in
val _ = emitML (!Globals.emitMLDir) ("int",
  OPEN ["num", "words"]
  :: EQDATATYPE ([], `int = int_of_num of num | neg_int_of_num of num`)
  :: MLSIG "type num = numML.num"
  :: MLSIG "type 'a itself = 'a fcpML.itself"
  :: MLSIG "type 'a word = 'a wordsML.word"
  :: MLSIG "val int_of_num : num -> int"
  :: MLSIG "val fromInt : Int.int -> int"
  :: MLSIG "val toInt : int -> Int.int option"
  :: MLSIG "val fromString : string -> int"
  :: MLSTRUCT
        "fun fromString s =\n\
      \    let val s = String.extract(s,0,SOME (Int.-(String.size s,1))) in\n\
      \      if String.sub(s,0) = #\"-\" then\n\
      \        let val s = String.extract(s,1,NONE) in\n\
      \          neg_int_of_num (numML.PRE (numML.fromString s))\n\
      \        end\n\
      \      else\n\
      \        int_of_num (numML.fromString s)\n\
      \    end\n"
  :: MLSTRUCT
        "fun fromInt i =\n\
      \    fromString (String.map (fn c => if c = #\"~\" then #\"-\" else c)\n\
      \      (String.^(Int.toString i,\"i\")))\n"
  :: MLSTRUCT
        "fun toInt (int_of_num n) = numML.toInt n\n\
      \    | toInt (neg_int_of_num n) =\n\
      \         case numML.toInt n of\n\
      \           SOME v => SOME (Int.-(Int.~ v,1))\n\
      \         | NONE => NONE\n"
  :: map (DEFN o wordsLib.WORDS_EMIT_RULE) [INT_NEG_EMIT, INT_Num_EMIT,
       INT_LT_EMIT, INT_LE_CALCULATE, INT_GT_CALCULATE, INT_GE_CALCULATE,
       INT_ADD_EMIT, INT_SUB_EMIT, INT_MUL_EMIT, INT_EXP_EMIT,
       INT_DIV_EMIT, INT_MOD_EMIT, INT_QUOTE_EMIT, INT_REM_EMIT,
       INT_MAX_def, INT_MIN_def, UINT_MAX_def, i2w_itself, w2i_def])
end;

val _ = export_theory()

