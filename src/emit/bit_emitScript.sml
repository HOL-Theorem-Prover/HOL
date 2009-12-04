open HolKernel boolLib bossLib Parse;
open EmitML numeralTheory arithmeticTheory bitTheory numeral_bitTheory;
open num_emitTheory list_emitTheory string_emitTheory;

val _ = new_theory "bit_emit";

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val PRE = prim_recTheory.PRE;
val NOT_SUC = numTheory.NOT_SUC;

val NUMERAL_1 = Q.prove(
  `!n. (NUMERAL (BIT1 n) = 1) = (n = 0)`,
  REWRITE_TAC [GSYM (REWRITE_CONV [GSYM ALT_ZERO] ``NUMERAL (BIT1 0)``)]
    \\ SIMP_TAC bool_ss [BIT1, NUMERAL_DEF]
    \\ DECIDE_TAC);

val NUMERAL_1b = Q.prove(
  `!n. ~(NUMERAL (BIT2 n) = 1)`,
  REWRITE_TAC [GSYM (REWRITE_CONV [GSYM ALT_ZERO] ``NUMERAL (BIT1 0)``)]
    \\ SIMP_TAC bool_ss [BIT1, BIT2, NUMERAL_DEF]
    \\ DECIDE_TAC);

val iDUB_SUC = Q.prove(`!n. numeral$iDUB (SUC n) = BIT2 n`,
  SIMP_TAC bool_ss [iDUB, BIT2, ADD1] \\ DECIDE_TAC);

val DIV2_BIT1_SUC = Q.prove(
  `!n. DIV2 (NUMERAL (BIT1 (SUC n))) = n + 1`,
  REWRITE_TAC [DIV2_def]
    \\ GEN_REWRITE_TAC (DEPTH_CONV o RATOR_CONV o RAND_CONV) empty_rewrites
         [BIT1, Q.SPEC `BIT1 (SUC n)` NUMERAL_DEF]
    \\ SIMP_TAC arith_ss [ADD1, ONCE_REWRITE_RULE [MULT_COMM] ADD_DIV_ADD_DIV]);

val LOG2_compute = Q.prove(
  `!n. LOG2 n =
         if n = 0 then
           FAIL LOG2 ^(mk_var("undefined",bool)) n
         else
           if n = 1 then
             0
           else
             1 + LOG2 (DIV2 n)`,
  Cases \\ REWRITE_TAC [NOT_SUC, combinTheory.FAIL_THM]
    \\ Q.SPEC_TAC (`n'`,`n`) \\ CONV_TAC numLib.SUC_TO_NUMERAL_DEFN_CONV
    \\ STRIP_TAC
    << [
       REWRITE_TAC [NUMERAL_1] \\ Cases \\ RW_TAC arith_ss [numeral_log2]
         << [PROVE_TAC [iDUB_removal, numeral_ilog2, ALT_ZERO],
             REWRITE_TAC [iDUB_SUC, DIV2_BIT1_SUC, numeral_ilog2]
               \\ SIMP_TAC arith_ss [iLOG2_def]],
       REWRITE_TAC [NUMERAL_1b, numeral_div2, numeral_ilog2, numeral_log2,
                    NUMERAL_DEF, iLOG2_def, ADD1]]);

val BITWISE_compute = Q.prove(
  `!n opr a b.
      BITWISE n opr a b =
        if n = 0 then 0 else
          2 * BITWISE (PRE n) opr (DIV2 a) (DIV2 b) +
          (if opr (ODD a) (ODD b) then 1 else 0)`,
  Cases >> REWRITE_TAC [CONJUNCT1 BITWISE_def]
    \\ REWRITE_TAC
         [DIV2_def, NOT_SUC, PRE, EXP, BITWISE_EVAL, LSB_ODD, SBIT_def]);

val BIT_MODF_compute = Q.prove(
  `!n f x b e y.
      BIT_MODF n f x b e y =
        if n = 0 then y else
          BIT_MODF (PRE n) f (DIV2 x) (b + 1) (2 * e)
           (if f b (ODD x) then e + y else y)`,
  Cases \\ REWRITE_TAC [DIV2_def, NOT_SUC, PRE, BIT_MODF_def]);

val BIT_REV_compute = Q.prove(
  `!n x y.
      BIT_REV n x y =
        if n = 0 then y else
          BIT_REV (PRE n) (DIV2 x) (2 * y + (if ODD x then 1 else 0))`,
  Cases \\ REWRITE_TAC [DIV2_def, NOT_SUC, PRE, BIT_REV_def, EXP, SBIT_def]);

val TIMES_2EXP_lem = Q.prove(
  `!n. FUNPOW numeral$iDUB n 1 = 2 ** n`,
  Induct \\ ASM_SIMP_TAC arith_ss
    [EXP,CONJUNCT1 FUNPOW,FUNPOW_SUC,iDUB,GSYM TIMES2]);

val TIMES_2EXP_compute = Q.prove(
  `!n x. TIMES_2EXP n x = if x = 0 then 0 else x * FUNPOW numeral$iDUB n 1`,
  RW_TAC bool_ss [MULT, TIMES_2EXP_lem, CONJUNCT1 FUNPOW, TIMES_2EXP_def]);

val TIMES_2EXP1 =
  (GSYM o REWRITE_RULE [arithmeticTheory.MULT_LEFT_1] o
   Q.SPECL [`x`,`1`]) bitTheory.TIMES_2EXP_def;

val MOD_2EXP_EQ_compute = Q.prove(
  `!n a b. MOD_2EXP_EQ n a b =
             if n = 0 then T else
               (ODD a = ODD b) /\ MOD_2EXP_EQ (n - 1) (DIV2 a) (DIV2 b)`,
  Cases \\ SRW_TAC [] [MOD_2EXP_EQ])

val BOOLIFY_compute = Q.prove(
  `!n. BOOLIFY n m a =
         if n = 0 then
           a
         else
           BOOLIFY (PRE n) (DIV2 m) (ODD m::a)`,
  Cases THEN SRW_TAC [] [BOOLIFY_def]);

val HEX_compute = Q.prove(
  `!n. HEX n =
          if n = 0 then #"0"
     else if n = 1 then #"1"
     else if n = 2 then #"2"
     else if n = 3 then #"3"
     else if n = 4 then #"4"
     else if n = 5 then #"5"
     else if n = 6 then #"6"
     else if n = 7 then #"7"
     else if n = 8 then #"8"
     else if n = 9 then #"9"
     else if n = 10 then #"A"
     else if n = 11 then #"B"
     else if n = 12 then #"C"
     else if n = 13 then #"D"
     else if n = 14 then #"E"
     else if n = 15 then #"F"
     else FAIL HEX ^(mk_var("not a hex digit",bool)) n`,
  SRW_TAC [] [HEX_def,combinTheory.FAIL_THM]);

val UNHEX_compute = Q.prove(
  `!n. UNHEX c =
          if c = #"0" then 0
     else if c = #"1" then 1
     else if c = #"2" then 2
     else if c = #"3" then 3
     else if c = #"4" then 4
     else if c = #"5" then 5
     else if c = #"6" then 6
     else if c = #"7" then 7
     else if c = #"8" then 8
     else if c = #"9" then 9
     else if c = #"A" then 10
     else if c = #"B" then 11
     else if c = #"C" then 12
     else if c = #"D" then 13
     else if c = #"E" then 14
     else if c = #"F" then 15
     else FAIL UNHEX ^(mk_var("not a hex digit",bool)) c`,
  SRW_TAC [] [UNHEX_def,combinTheory.FAIL_THM])

val LOWEST_SET_BIT_emit = Q.prove(
  `!n. LOWEST_SET_BIT n =
         if n = 0 then
           FAIL LOWEST_SET_BIT ^(mk_var("zero value",bool)) n
         else if ODD n then
           0
         else
           1 + LOWEST_SET_BIT (DIV2 n)`,
  SRW_TAC [] [LOWEST_SET_BIT, combinTheory.FAIL_THM]);

val defs =
  map (DEFN o PURE_REWRITE_RULE [TIMES_2EXP1])
       [TIMES_2EXP_compute,BITWISE_compute,LOG_compute,LOWEST_SET_BIT_emit,
        l2n_def,n2l_def,s2n_compute,n2s_compute,HEX_compute,UNHEX_compute,
        num_from_bin_list_def,num_from_oct_list_def,num_from_dec_list_def,
        num_from_hex_list_def,num_to_bin_list_def,num_to_oct_list_def,
        num_to_dec_list_def,num_to_hex_list_def,num_from_bin_string_def,
        num_from_oct_string_def,num_from_dec_string_def,num_from_hex_string_def,
        num_to_bin_string_def,num_to_oct_string_def,num_to_dec_string_def,
        num_to_hex_string_def,
        BIT_MODF_compute, BIT_MODIFY_EVAL,
        BIT_REV_compute, BIT_REVERSE_EVAL,
        LOG2_compute, DIVMOD_2EXP, SBIT_def, BITS_def, MOD_2EXP_EQ_compute,
        BITV_def, BIT_def, SLICE_def, LSB_def, SIGN_EXTEND_def, BOOLIFY_compute]

val _ = eSML "bit"
  (MLSIG  "type num = numML.num" ::
   OPEN ["num"] ::
   defs)

val _ = eCAML "bit"
  (MLSIGSTRUCT ["type num = NumML.num"] @
   OPEN ["num"] ::
   defs)

val _ = export_theory ();
