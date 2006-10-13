(* app load ["wordUtil","bitsTheory"]; *)
open HolKernel Parse boolLib bossLib Q wordUtil
     arithmeticTheory numeralTheory bitsTheory;

val arith_ss = old_arith_ss

(* -------------------------------------------------------- *)

val _ = new_theory "numeral_bits";

(* -------------------------------------------------------- *)

val SUC_RULE = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV;

(* -------------------------------------------------------- *)

val SIMP_BIT1 = (GSYM o SIMP_RULE arith_ss []) BIT1;

val iBITWISE_def =
  Definition.new_definition("iBITWISE_def", ``iBITWISE = BITWISE``);

val iBITWISE = prove(
  `(!opr a b. iBITWISE 0 opr a b = ZERO) /\
   (!x opr a b.
     iBITWISE (SUC x) opr a b =
       let w = iBITWISE x opr (DIV2 a) (DIV2 b) in
       if opr (ODD a) (ODD b) then BIT1 w else numeral$iDUB w)`,
  RW_TAC arith_ss [iBITWISE_def,iDUB,SIMP_BIT1,SBIT_def,EXP,
                   LSB_ODD,GSYM DIV2_def,BITWISE_EVAL,LET_THM]
    THEN REWRITE_TAC [BITWISE_def,ALT_ZERO]
);

val iBITWISE = save_thm("iBITWISE", SUC_RULE iBITWISE);

val NUMERAL_BITWISE = store_thm("NUMERAL_BITWISE",
  `(!x opr a. BITWISE x opr 0 0 = NUMERAL (iBITWISE x opr 0 0)) /\
   (!x opr a. BITWISE x opr (NUMERAL a) 0 = NUMERAL (iBITWISE x opr (NUMERAL a) 0)) /\
   (!x opr b. BITWISE x opr 0 (NUMERAL b) = NUMERAL (iBITWISE x opr 0 (NUMERAL b))) /\
    !x opr a b. BITWISE x opr (NUMERAL a) (NUMERAL b) = NUMERAL (iBITWISE x opr (NUMERAL a) (NUMERAL b))`,
  REWRITE_TAC [iBITWISE_def,NUMERAL_DEF]
);

val NUMERAL_DIV2 = store_thm("NUMERAL_DIV2",
   `(DIV2 0 = 0) /\
     (!n. DIV2 (NUMERAL (BIT1 n)) = NUMERAL n) /\
     (!n. DIV2 (NUMERAL (BIT2 n)) = NUMERAL (SUC n))`,
  RW_TAC bool_ss [ALT_ZERO,NUMERAL_DEF,BIT1,BIT2]
    THEN SIMP_TAC arith_ss [DIV2_def,ONCE_REWRITE_RULE [MULT_COMM] ADD_DIV_ADD_DIV]
);

val DIV_2EXP = prove(
  `(!n. DIV_2EXP 0 n = n) /\
   (!x. DIV_2EXP x 0 = 0) /\
   (!x n. DIV_2EXP (SUC x) (NUMERAL n) = DIV_2EXP x (DIV2 (NUMERAL n)))`,
  RW_TAC arith_ss [DIV_2EXP_def,DIV2_def,EXP,ZERO_DIV,DIV_DIV_DIV_MULT,ZERO_LT_TWOEXP]
);

val NUMERAL_DIV_2EXP = save_thm("NUMERAL_DIV_2EXP", SUC_RULE DIV_2EXP);

(* -------------------------------------------------------- *)

val iLOG2_def =
 Definition.new_definition("iLOG2_def", ``iLOG2 n = LOG2 (n + 1)``);

val LOG2_1 = (SIMP_RULE arith_ss [] o SPECL [`1`,`0`]) LOG2_UNIQUE;
val LOG2_BIT2 = (GEN_ALL o SIMP_RULE arith_ss [LEFT_ADD_DISTRIB] o
                 ONCE_REWRITE_RULE [DECIDE ``!a b. (a = b) = (2 * a = 2 * b)``] o
                 SIMP_RULE arith_ss [] o SPEC `n + 1`) LOG2;
val LOG2_BIT1 = (REWRITE_RULE [DECIDE ``!a. a + 2 + 1 = a + 3``] o
                 ONCE_REWRITE_RULE [DECIDE ``!a b. (a = b) = (a + 1 = b + 1)``]) LOG2_BIT2;

val LESS_MULT_MONO_2 =
   (GEN_ALL o numLib.REDUCE_RULE o INST [`n` |-> `1`] o SPEC_ALL) LESS_MULT_MONO;

val lem = prove(
  `!a b. 2 * (a MOD 2 ** b) < 2 ** (b + 1)`,
  METIS_TAC [MOD_2EXP_LT,ADD1,EXP,LESS_MULT_MONO_2]
);

val lem2 = prove(
  `!a b. 2 * (a MOD 2 ** b) + 1 < 2 ** (b + 1)`,
  METIS_TAC [MOD_2EXP_LT,ADD1,EXP,LESS_MULT_MONO_2,
    DECIDE ``a < b ==> 2 * a + 1 < 2 * b``]
);

val numeral_ilog2 = store_thm("numeral_ilog2",
  `(iLOG2 ZERO = 0) /\
   (!n. iLOG2 (BIT1 n) = 1 + iLOG2 n) /\
   (!n. iLOG2 (BIT2 n) = 1 + iLOG2 n)`,
  RW_TAC bool_ss [ALT_ZERO,NUMERAL_DEF,BIT1,BIT2,iLOG2_def]
    THEN SIMP_TAC arith_ss [LOG2_1]
    THENL [
      MATCH_MP_TAC ((SIMP_RULE arith_ss [] o
        SPECL [`2 * n + 2`,`LOG2 (n + 1) + 1`]) LOG2_UNIQUE)
        THEN EXISTS_TAC `2 * ((n + 1) MOD 2 ** LOG2 (n + 1))`
        THEN SIMP_TAC arith_ss [LOG2_BIT2,EXP_ADD,lem],
      MATCH_MP_TAC ((SIMP_RULE arith_ss [] o
        SPECL [`2 * n + 3`,`LOG2 (n + 1) + 1`]) LOG2_UNIQUE)
        THEN EXISTS_TAC `2 * ((n + 1) MOD 2 ** LOG2 (n + 1)) + 1`
        THEN SIMP_TAC arith_ss [LOG2_BIT1,EXP_ADD,lem2]
    ]
);

val numeral_log2 = store_thm("numeral_log2",
  `(!n. LOG2 (NUMERAL (BIT1 n)) = iLOG2 (numeral$iDUB n)) /\
   (!n. LOG2 (NUMERAL (BIT2 n)) = iLOG2 (BIT1 n))`,
  RW_TAC bool_ss [ALT_ZERO,NUMERAL_DEF,BIT1,BIT2,iLOG2_def,numeralTheory.iDUB]
    THEN SIMP_TAC arith_ss []
);

(* -------------------------------------------------------- *)

val _ = export_theory();
val _ = export_doc_theorems();

(* -------------------------------------------------------- *)
