(* app load ["wordUtil","bitsTheory"]; *)
open HolKernel boolLib bossLib Q wordUtil
     arithmeticTheory numeralTheory bitsTheory;

(* -------------------------------------------------------- *)

val _ = new_theory "numeral_bits";

(* -------------------------------------------------------- *)

val SUC_RULE = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV;

(* -------------------------------------------------------- *)

val iMOD_2EXP_def = Define`
  (iMOD_2EXP 0 n = 0) /\
  (iMOD_2EXP (SUC x) n =
      2 * (iMOD_2EXP x (n DIV 2)) + SBIT (ODD n) 0)`;

val iBITWISE_def = Define `iBITWISE = BITWISE`;

(* -------------------------------------------------------- *)

val SIMP_BIT1 = (GSYM o SIMP_RULE arith_ss []) BIT1;

val iBITWISE = prove(
  `(!opr a b. iBITWISE 0 opr a b = ZERO) /\
   (!x opr a b.
     iBITWISE (SUC x) opr a b =
       let w = iBITWISE x opr (DIV2 a) (DIV2 b) in
       if opr (ODD a) (ODD b) then BIT1 w else iDUB w)`,
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

val ADD_DIV_ADD_DIV2 = (GEN_ALL o ONCE_REWRITE_RULE [MULT_COMM] o
                        SIMP_RULE arith_ss [GSYM ADD1] o SPECL [`n`,`1`] o
                        SIMP_RULE bool_ss [DECIDE (Term `0 < 2`)] o SPEC `2`) ADD_DIV_ADD_DIV;

val SPEC_MOD_COMMON_FACTOR = (GEN_ALL o SIMP_RULE arith_ss [GSYM EXP,ZERO_LT_TWOEXP] o
            SPECL [`2`,`m`,`2 ** SUC h`]) MOD_COMMON_FACTOR;
val SPEC_MOD_COMMON_FACTOR2 = (GEN_ALL o SYM o SIMP_RULE arith_ss [GSYM EXP,ZERO_LT_TWOEXP] o
            SPECL [`2`,`m`,`2 ** h`]) MOD_COMMON_FACTOR;

val SPEC_MOD_PLUS = (GEN_ALL o GSYM o SIMP_RULE bool_ss [ZERO_LT_TWOEXP] o SPEC `2 EXP n`) MOD_PLUS;
val SPEC_TWOEXP_MONO = (GEN_ALL o SIMP_RULE arith_ss [] o SPECL [`0`,`SUC b`]) TWOEXP_MONO;

val lem = prove(
  `!m n. (2 * m) MOD 2 ** SUC n + 1 < 2 ** SUC n`,
  RW_TAC arith_ss [SPEC_MOD_COMMON_FACTOR2,EXP,DOUBLE_LT,MOD_2EXP_LT,
                   (GEN_ALL o numLib.REDUCE_RULE o SPECL [`m`,`i`,`1`]) LESS_MULT_MONO]
);

val BITS_SUC2 = prove(
  `!h n. BITS (SUC h) 0 n = 2 * BITS h 0 (n DIV 2) + SBIT (ODD n) 0`,
  RW_TAC arith_ss [SBIT_def]
    THEN FULL_SIMP_TAC arith_ss [GSYM EVEN_ODD,EVEN_EXISTS,ODD_EXISTS,BITS_ZERO3,ADD_DIV_ADD_DIV2,
                                 ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV,SPEC_MOD_COMMON_FACTOR]
    THEN SUBST1_TAC (SPEC `2 * m` ADD1)
    THEN ONCE_REWRITE_TAC [SPEC_MOD_PLUS]
    THEN SIMP_TAC bool_ss [LESS_MOD,ZERO_LT_TWOEXP,SPEC_TWOEXP_MONO,LESS_MOD,lem]
);

val MOD_2EXP_ZERO = prove(
  `!x. MOD_2EXP x 0 = 0`,
  SIMP_TAC arith_ss [MOD_2EXP_def,ZERO_MOD,ZERO_LT_TWOEXP]
);

val iMOD_2EXP = prove(
  `!x n. MOD_2EXP x (NUMERAL n) = NUMERAL (iMOD_2EXP x n)`,
  REWRITE_TAC [NUMERAL_DEF]
    THEN Induct
    THEN1 SIMP_TAC arith_ss [iMOD_2EXP_def,MOD_2EXP_def]
    THEN STRIP_TAC THEN REWRITE_TAC [iMOD_2EXP_def]
    THEN POP_ASSUM (SUBST1_TAC o SYM o SPEC `n DIV 2`)
    THEN Cases_on `x`
    THEN1 (SIMP_TAC arith_ss [MOD_2EXP_def,MOD_2,EVEN_ODD,SBIT_def] THEN PROVE_TAC [])
    THEN REWRITE_TAC [(GSYM o REWRITE_RULE [GSYM MOD_2EXP_def]) BITS_ZERO3,BITS_SUC2]
);

val iMOD_2EXP_CLAUSES = prove(
  `(!n. iMOD_2EXP 0 n = ZERO) /\
   (!x n. iMOD_2EXP x ZERO = ZERO) /\
   (!x n. iMOD_2EXP (SUC x) (BIT1 n) = BIT1 (iMOD_2EXP x n)) /\
   (!x n. iMOD_2EXP (SUC x) (BIT2 n) = iDUB (iMOD_2EXP x (SUC n)))`,
  RW_TAC arith_ss [iMOD_2EXP_def,iDUB,SBIT_def,numeral_evenodd,GSYM DIV2_def,
                   REWRITE_RULE [SYM ALT_ZERO,NUMERAL_DEF,ADD1] NUMERAL_DIV2]
    THENL [
      REWRITE_TAC [ALT_ZERO],
      REWRITE_TAC [ALT_ZERO]
        THEN REWRITE_TAC [MOD_2EXP_ZERO,(GSYM o REWRITE_RULE [NUMERAL_DEF]) iMOD_2EXP],
      SIMP_TAC arith_ss [SPEC `iMOD_2EXP x n` BIT1],
      ONCE_REWRITE_TAC [(SYM o REWRITE_CONV [NUMERAL_DEF]) ``1``]
        THEN REWRITE_TAC [ADD1]
    ]
);

val iMOD_2EXP = save_thm("iMOD_2EXP",CONJ MOD_2EXP_ZERO iMOD_2EXP);

val NUMERAL_MOD_2EXP = save_thm("NUMERAL_MOD_2EXP", SUC_RULE iMOD_2EXP_CLAUSES);

(* -------------------------------------------------------- *)

val _ = 
 let open EmitML
 in exportML("numeral_bits", 
     MLSIG  "type num = numML.num" :: OPEN ["num"] 
     ::
     map (DEFN o PURE_REWRITE_RULE [arithmeticTheory.NUMERAL_DEF])
         [NUMERAL_DIV2,iBITWISE, NUMERAL_BITWISE,
          NUMERAL_MOD_2EXP,iMOD_2EXP, NUMERAL_DIV_2EXP])
 end;

val _ = export_theory();
val _ = export_doc_theorems();

(* -------------------------------------------------------- *)
