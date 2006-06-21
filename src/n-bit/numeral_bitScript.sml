(* ========================================================================= *)
(* FILE          : numeral_bitScript.sml                                     *)
(* DESCRIPTION   : Theorems providing numeral based evaluation of            *)
(*                 functions in bitTheory                                    *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2001-2005                                                 *)
(* ========================================================================= *)

(* interactive use:
  load "bitTheory";
*)

open HolKernel Parse boolLib bossLib;
open Q arithmeticTheory numeralTheory;
open bitTheory;

val _ = new_theory "numeral_bit";

(* ------------------------------------------------------------------------- *)

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

(* ------------------------------------------------------------------------- *)

val BIT_REV_def =
  Prim_rec.new_recursive_definition
  {name = "BIT_REV_def",
   def = ``(BIT_REV 0 x y = y)
        /\ (BIT_REV (SUC n) x y =
              BIT_REV n (x DIV 2) (2 * y + SBIT (ODD x) 0))``,
   rec_axiom = prim_recTheory.num_Axiom};

val BIT_R = ``\(x,y). (x DIV 2, 2 * y + SBIT (BIT 0 x) 0)``;

val BIT_R_FUNPOW = prove(
  `!n x y. FUNPOW ^BIT_R (SUC n) (x,y) =
   (x DIV 2 ** (SUC n), 2 * (SND (FUNPOW ^BIT_R n (x, y))) + SBIT (BIT n x) 0)`,
  Induct >> SIMP_TAC arith_ss [FUNPOW]
    \\ `!x n. BIT 0 (x DIV 2 ** n) = BIT n x`
      by SIMP_TAC std_ss [BIT_def,BITS_THM,BITS_COMP_THM2,DIV_1,SUC_SUB]
    \\ ASM_SIMP_TAC std_ss [FUNPOW_SUC,DIV_DIV_DIV_MULT,ZERO_LT_TWOEXP,
           (GSYM o ONCE_REWRITE_RULE [MULT_COMM]) EXP]);

val BIT_R_BIT_REV = prove(
  `!n a y. SND (FUNPOW ^BIT_R n (a, y)) = BIT_REV n a y`,
  Induct >> SIMP_TAC std_ss [FUNPOW,BIT_REV_def]
    \\ ASM_SIMP_TAC std_ss [FUNPOW,BIT_REV_def,LSB_def,GSYM LSB_ODD]);

val BIT_REVERSE_REV = prove(
  `!m n. BIT_REVERSE m n = SND (FUNPOW ^BIT_R m (n, 0))`,
  Induct >> SIMP_TAC std_ss [BIT_REVERSE_def,FUNPOW]
    \\ ASM_SIMP_TAC arith_ss [BIT_REVERSE_def,BIT_R_FUNPOW]);

val BIT_REVERSE_EVAL = save_thm("BIT_REVERSE_EVAL",
  REWRITE_RULE [BIT_R_BIT_REV] BIT_REVERSE_REV);

(* ------------------------------------------------------------------------- *)

val BIT_MODF_def =
  Prim_rec.new_recursive_definition
  {name = "BIT_MODF_def",
   def = ``(BIT_MODF 0 f x b e y = y)
        /\ (BIT_MODF (SUC n) f x b e y =
              BIT_MODF n f (x DIV 2) (b + 1) (2 * e)
                (if f b (ODD x) then e + y else y))``,
   rec_axiom = prim_recTheory.num_Axiom};

val BIT_M =
  ``\(y,f,x,b,e).
       (if f b (BIT 0 x) then e + y else y, f, x DIV 2, b + 1, 2 * e)``;

val BIT_M_FUNPOW = prove(
  `!n f x b e y. FUNPOW ^BIT_M (SUC n) (y,f,x,b,e) =
       (if f (b + n) (BIT n x)
        then 2 ** n * e + FST (FUNPOW ^BIT_M n (y,f,x,b,e))
        else FST (FUNPOW ^BIT_M n (y,f,x,b,e)),
        f, x DIV 2 ** (SUC n), b + SUC n, 2 ** SUC n * e)`,
  Induct >> SIMP_TAC arith_ss [FUNPOW]
    \\ `!x n. BIT 0 (x DIV 2 ** n) = BIT n x`
      by SIMP_TAC std_ss [BIT_def,BITS_THM,BITS_COMP_THM2,DIV_1,SUC_SUB]
    \\ ASM_SIMP_TAC arith_ss [FUNPOW_SUC,DIV_DIV_DIV_MULT,ZERO_LT_TWOEXP,
           (GSYM o ONCE_REWRITE_RULE [MULT_COMM]) EXP]
    \\ SIMP_TAC (std_ss++numSimps.ARITH_AC_ss) [EXP]);

val BIT_M_BIT_MODF = prove(
  `!n f x b e y. FST (FUNPOW ^BIT_M n (y,f,x,b,e)) = BIT_MODF n f x b e y`,
  Induct >> SIMP_TAC std_ss [FUNPOW,BIT_MODF_def]
    \\ ASM_SIMP_TAC std_ss [FUNPOW,BIT_MODF_def,LSB_def,GSYM LSB_ODD]);

val BIT_MODIFY_MODF = prove(
  `!m f n. BIT_MODIFY m f n = FST (FUNPOW ^BIT_M m (0,f,n,0,1))`,
  Induct >> SIMP_TAC std_ss [BIT_MODIFY_def,FUNPOW]
    \\ RW_TAC arith_ss [SBIT_def,BIT_MODIFY_def,BIT_M_FUNPOW]);

val BIT_MODIFY_EVAL = save_thm("BIT_MODIFY_EVAL",
  REWRITE_RULE [BIT_M_BIT_MODF] BIT_MODIFY_MODF);

(* ------------------------------------------------------------------------- *)

val SUC_RULE = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV;

val iMOD_2EXP_def =
 Prim_rec.new_recursive_definition
  {name = "iMOD_2EXP_def",
   def = ``(iMOD_2EXP 0 n = 0) /\
           (iMOD_2EXP (SUC x) n =
              2 * (iMOD_2EXP x (n DIV 2)) + SBIT (ODD n) 0)``,
   rec_axiom = prim_recTheory.num_Axiom};

val iBITWISE_def =
  Definition.new_definition("iBITWISE_def", ``iBITWISE = BITWISE``);

val SIMP_BIT1 = (GSYM o SIMP_RULE arith_ss []) BIT1;

val iBITWISE = prove(
  `(!opr a b. iBITWISE 0 opr a b = ZERO) /\
   (!x opr a b.
     iBITWISE (SUC x) opr a b =
       let w = iBITWISE x opr (DIV2 a) (DIV2 b) in
       if opr (ODD a) (ODD b) then BIT1 w else iDUB w)`,
  RW_TAC arith_ss [iBITWISE_def,iDUB,SIMP_BIT1,SBIT_def,EXP,
                   LSB_ODD,GSYM DIV2_def,BITWISE_EVAL,LET_THM]
    \\ REWRITE_TAC [BITWISE_def,ALT_ZERO]);

val iBITWISE = save_thm("iBITWISE", SUC_RULE iBITWISE);

val NUMERAL_BITWISE = store_thm("NUMERAL_BITWISE",
  `(!x f a. BITWISE x f 0 0 = NUMERAL (iBITWISE x f 0 0)) /\
   (!x f a. BITWISE x f (NUMERAL a) 0 =
              NUMERAL (iBITWISE x f (NUMERAL a) 0)) /\
   (!x f b. BITWISE x f 0 (NUMERAL b) =
              NUMERAL (iBITWISE x f 0 (NUMERAL b))) /\
    !x f a b. BITWISE x f (NUMERAL a) (NUMERAL b) =
                 NUMERAL (iBITWISE x f (NUMERAL a) (NUMERAL b))`,
  REWRITE_TAC [iBITWISE_def,NUMERAL_DEF]);

val NUMERAL_DIV2 = store_thm("NUMERAL_DIV2",
   `(DIV2 0 = 0) /\
     (!n. DIV2 (NUMERAL (BIT1 n)) = NUMERAL n) /\
     (!n. DIV2 (NUMERAL (BIT2 n)) = NUMERAL (SUC n))`,
  RW_TAC bool_ss [ALT_ZERO,NUMERAL_DEF,BIT1,BIT2]
    \\ SIMP_TAC arith_ss [DIV2_def,
           ONCE_REWRITE_RULE [MULT_COMM] ADD_DIV_ADD_DIV]);

val DIV_2EXP = prove(
  `(!n. DIV_2EXP 0 n = n) /\
   (!x. DIV_2EXP x 0 = 0) /\
   (!x n. DIV_2EXP (SUC x) (NUMERAL n) =
            DIV_2EXP x (DIV2 (NUMERAL n)))`,
  RW_TAC arith_ss [DIV_2EXP_def,DIV2_def,EXP,ZERO_DIV,
    DIV_DIV_DIV_MULT,ZERO_LT_TWOEXP]);

val NUMERAL_DIV_2EXP = save_thm("NUMERAL_DIV_2EXP", SUC_RULE DIV_2EXP);

val NUMERAL_BIT_REV = prove(
  `(!x y. BIT_REV 0 x y = y) /\
   (!n y. BIT_REV (SUC n) 0 y = BIT_REV n 0 (iDUB y)) /\
   (!n x y. BIT_REV (SUC n) (NUMERAL x) y =
      BIT_REV n (DIV2 (NUMERAL x)) (if ODD x then BIT1 y else iDUB y))`,
  RW_TAC bool_ss [BIT_REV_def,SBIT_def,NUMERAL_DEF,DIV2_def,
           ADD,ADD_0,BIT2,BIT1,iDUB,ALT_ZERO]
    \\ FULL_SIMP_TAC arith_ss []);

val NUMERAL_BIT_REV = save_thm("NUMERAL_BIT_REV", SUC_RULE NUMERAL_BIT_REV);

val NUMERAL_BIT_REVERSE = store_thm("NUMERAL_BIT_REVERSE",
  `(!m. BIT_REVERSE (NUMERAL m) 0 = NUMERAL (BIT_REV (NUMERAL m) 0 ZERO)) /\
    !n m. BIT_REVERSE (NUMERAL m) (NUMERAL n) =
       NUMERAL (BIT_REV (NUMERAL m) (NUMERAL n) ZERO)`,
  SIMP_TAC bool_ss [NUMERAL_DEF,ALT_ZERO,BIT_REVERSE_EVAL]);

val NUMERAL_BIT_MODF = prove(
  `(!f x b e y. BIT_MODF 0 f x b e y = y) /\
   (!n f b e y. BIT_MODF (SUC n) f 0 b (NUMERAL e) y =
      BIT_MODF n f 0 (b + 1) (NUMERAL (iDUB e))
              (if f b F then (NUMERAL e) + y else y)) /\
   (!n f x b e y. BIT_MODF (SUC n) f (NUMERAL x) b (NUMERAL e) y =
      BIT_MODF n f (DIV2 (NUMERAL x)) (b + 1) (NUMERAL (iDUB e))
              (if f b (ODD x) then (NUMERAL e) + y else y))`,
  RW_TAC bool_ss [BIT_MODF_def,SBIT_def,NUMERAL_DEF,DIV2_def,
           ADD,ADD_0,BIT2,BIT1,iDUB,ALT_ZERO]
    \\ FULL_SIMP_TAC arith_ss []);

val NUMERAL_BIT_MODF = save_thm("NUMERAL_BIT_MODF", SUC_RULE NUMERAL_BIT_MODF);

val NUMERAL_BIT_MODIFY = store_thm("NUMERAL_BIT_MODIFY",
  `(!m f. BIT_MODIFY (NUMERAL m) f 0 = BIT_MODF (NUMERAL m) f 0 0 1 0) /\
    !m f n. BIT_MODIFY (NUMERAL m) f (NUMERAL n) =
       BIT_MODF (NUMERAL m) f (NUMERAL n) 0 1 0`,
  SIMP_TAC bool_ss [NUMERAL_DEF,ALT_ZERO,BIT_MODIFY_EVAL]);

(* ------------------------------------------------------------------------- *)

val ADD_DIV_ADD_DIV2 = (GEN_ALL o
  SIMP_RULE arith_ss [GSYM ADD1] o SPECL [`n`,`1`] o
  SIMP_RULE bool_ss [DECIDE (Term `0 < 2`)] o SPEC `2`) ADD_DIV_ADD_DIV;

val SPEC_MOD_COMMON_FACTOR = (GEN_ALL o
   SIMP_RULE arith_ss [GSYM EXP,ZERO_LT_TWOEXP] o
   SPECL [`2`,`m`,`2 ** SUC h`]) MOD_COMMON_FACTOR;

val SPEC_MOD_COMMON_FACTOR2 = (GEN_ALL o
   SYM o SIMP_RULE arith_ss [GSYM EXP,ZERO_LT_TWOEXP] o
   SPECL [`2`,`m`,`2 ** h`]) MOD_COMMON_FACTOR;

val SPEC_MOD_PLUS = (GEN_ALL o GSYM o
  SIMP_RULE bool_ss [ZERO_LT_TWOEXP] o SPEC `2 ** n`) MOD_PLUS;

val SPEC_TWOEXP_MONO = prove(
  `!a b. 1 < 2 ** SUC b`,
  METIS_TAC [EXP,prim_recTheory.LESS_0,EXP_BASE_LT_MONO,DECIDE ``1 < 2``])

val lem = prove(
  `!m n. (2 * m) MOD 2 ** SUC n + 1 < 2 ** SUC n`,
  RW_TAC arith_ss [SPEC_MOD_COMMON_FACTOR2,EXP,DOUBLE_LT,MOD_2EXP_LT,
    (GEN_ALL o numLib.REDUCE_RULE o SPECL [`m`,`i`,`1`]) LESS_MULT_MONO]);

val BITS_SUC2 = prove(
  `!h n. BITS (SUC h) 0 n = 2 * BITS h 0 (n DIV 2) + SBIT (ODD n) 0`,
  RW_TAC arith_ss [SBIT_def]
    \\ FULL_SIMP_TAC arith_ss [GSYM EVEN_ODD,EVEN_EXISTS,ODD_EXISTS,
         BITS_ZERO3,ADD_DIV_ADD_DIV2,SPEC_MOD_COMMON_FACTOR,
         ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
    \\ SUBST1_TAC (SPEC `2 * m` ADD1)
    \\ ONCE_REWRITE_TAC [SPEC_MOD_PLUS]
    \\ SIMP_TAC bool_ss [LESS_MOD,ZERO_LT_TWOEXP,SPEC_TWOEXP_MONO,LESS_MOD,lem]
);

val MOD_2EXP_ZERO = prove(
  `!x. MOD_2EXP x 0 = 0`,
  SIMP_TAC arith_ss [MOD_2EXP_def,ZERO_MOD,ZERO_LT_TWOEXP]);

val iMOD_2EXP = prove(
  `!x n. MOD_2EXP x (NUMERAL n) = NUMERAL (iMOD_2EXP x n)`,
  REWRITE_TAC [NUMERAL_DEF]
    \\ Induct
    >> SIMP_TAC arith_ss [iMOD_2EXP_def,MOD_2EXP_def]
    \\ STRIP_TAC \\ REWRITE_TAC [iMOD_2EXP_def]
    \\ POP_ASSUM (SUBST1_TAC o SYM o SPEC `n DIV 2`)
    \\ Cases_on `x`
    >> (SIMP_TAC arith_ss [MOD_2EXP_def,MOD_2,EVEN_ODD,SBIT_def]
             \\ PROVE_TAC [])
    \\ REWRITE_TAC [BITS_SUC2,(GSYM o REWRITE_RULE [GSYM MOD_2EXP_def])
           BITS_ZERO3]);

val iMOD_2EXP_CLAUSES = prove(
  `(!n. iMOD_2EXP 0 n = ZERO) /\
   (!x n. iMOD_2EXP x ZERO = ZERO) /\
   (!x n. iMOD_2EXP (SUC x) (BIT1 n) = BIT1 (iMOD_2EXP x n)) /\
   (!x n. iMOD_2EXP (SUC x) (BIT2 n) = iDUB (iMOD_2EXP x (SUC n)))`,
  RW_TAC arith_ss [iMOD_2EXP_def,iDUB,SBIT_def,numeral_evenodd,GSYM DIV2_def,
    REWRITE_RULE [SYM ALT_ZERO,NUMERAL_DEF,ADD1] NUMERAL_DIV2]
    << [
      REWRITE_TAC [ALT_ZERO],
      REWRITE_TAC [ALT_ZERO]
        \\ REWRITE_TAC [MOD_2EXP_ZERO,(GSYM o
               REWRITE_RULE [NUMERAL_DEF]) iMOD_2EXP],
      SIMP_TAC arith_ss [SPEC `iMOD_2EXP x n` BIT1],
      ONCE_REWRITE_TAC [(SYM o REWRITE_CONV [NUMERAL_DEF]) ``1``]
        \\ REWRITE_TAC [ADD1]]);

val iMOD_2EXP = save_thm("iMOD_2EXP",CONJ MOD_2EXP_ZERO iMOD_2EXP);

val NUMERAL_MOD_2EXP = save_thm("NUMERAL_MOD_2EXP",
  SUC_RULE iMOD_2EXP_CLAUSES);

val TIMES_2EXP_lem = prove(
  `!n. FUNPOW iDUB n 1 = 2 ** n`,
  Induct \\ ASM_SIMP_TAC arith_ss
    [EXP,CONJUNCT1 FUNPOW,FUNPOW_SUC,iDUB,GSYM TIMES2]);

val NUMERAL_TIMES_2EXP = store_thm("NUMERAL_TIMES_2EXP",
  `(!n. TIMES_2EXP n 0 = 0) /\ (!x. TIMES_2EXP 0 x = x) /\
  !x n. TIMES_2EXP (NUMERAL x) (NUMERAL n) =
     (NUMERAL n) * NUMERAL (FUNPOW iDUB (NUMERAL x) (BIT1 ZERO))`,
  `BIT1 ZERO = 1` by REWRITE_TAC [NUMERAL_DEF,BIT1,ALT_ZERO]
    \\ POP_ASSUM SUBST1_TAC
    \\ REWRITE_TAC [TIMES_2EXP_def,TIMES_2EXP_lem,NUMERAL_DEF]
    \\ SIMP_TAC std_ss [EXP]);

(* ------------------------------------------------------------------------- *)

val iLOG2_def =
 Definition.new_definition("iLOG2_def", ``iLOG2 n = LOG2 (n + 1)``);

val LOG2_1 = (SIMP_RULE arith_ss [] o SPECL [`1`,`0`]) LOG2_UNIQUE;

val numeral_ilog2 = store_thm("numeral_ilog2",
  `(iLOG2 ZERO = 0) /\
   (!n. iLOG2 (BIT1 n) = 1 + iLOG2 n) /\
   (!n. iLOG2 (BIT2 n) = 1 + iLOG2 n)`,
  RW_TAC bool_ss [ALT_ZERO,NUMERAL_DEF,BIT1,BIT2,iLOG2_def]
    \\ SIMP_TAC arith_ss [LOG2_1]
    << [
      MATCH_MP_TAC ((SIMP_RULE arith_ss [] o
              SPECL [`2 * n + 2`,`LOG2 (n + 1) + 1`]) LOG2_UNIQUE)
        \\ SIMP_TAC arith_ss [EXP_ADD,LOG2_def]
        \\ SIMP_TAC arith_ss [GSYM ADD1,EXP,logrootTheory.LOG,
            DECIDE ``(2 * n + 2 = (n + 1) * 2) /\ (2 * a < 4 * b = a < 2 * b)``]
        \\ SIMP_TAC arith_ss [GSYM EXP,logrootTheory.LOG],
      MATCH_MP_TAC ((SIMP_RULE arith_ss [] o
              SPECL [`2 * n + 3`,`LOG2 (n + 1) + 1`]) LOG2_UNIQUE)
        \\ SIMP_TAC arith_ss [EXP_ADD,LOG2_def]
        \\ SIMP_TAC arith_ss [GSYM ADD1,EXP,logrootTheory.LOG,
             DECIDE ``(2 * n + 3 = 2 * (n + 1) + 1)``,
             DECIDE ``a <= b ==> 2 * a <= SUC (2 * b)``]
        \\ SIMP_TAC arith_ss [
             DECIDE ``a < 2 * b ==> SUC (2 * a) < 4 * b``,
             (Once o GSYM) EXP,logrootTheory.LOG]]);

val numeral_log2 = store_thm("numeral_log2",
  `(!n. LOG2 (NUMERAL (BIT1 n)) = iLOG2 (iDUB n)) /\
   (!n. LOG2 (NUMERAL (BIT2 n)) = iLOG2 (BIT1 n))`,
  RW_TAC bool_ss [ALT_ZERO,NUMERAL_DEF,BIT1,BIT2,iLOG2_def,numeralTheory.iDUB]
    \\ SIMP_TAC arith_ss []);

(* ------------------------------------------------------------------------- *)

val TIMES_2EXP1 =
 (GSYM o REWRITE_RULE [arithmeticTheory.MULT_LEFT_1] o
  Q.SPECL [`x`,`1`]) bitTheory.TIMES_2EXP_def;

val _ =
 let open EmitML
 in exportML (!Globals.exportMLPath)
   ("bit",
     MLSIG  "type num = numML.num" :: OPEN ["num"]
     ::
     map (DEFN o PURE_REWRITE_RULE
         [arithmeticTheory.NUMERAL_DEF, TIMES_2EXP1,
          (GSYM o PURE_REWRITE_RULE [arithmeticTheory.NUMERAL_DEF])
             (CONJUNCT2 iMOD_2EXP),
          GSYM arithmeticTheory.ALT_ZERO,iBITWISE_def])
         [NUMERAL_DIV2,iBITWISE, NUMERAL_TIMES_2EXP,
          NUMERAL_BIT_MODF, NUMERAL_BIT_MODIFY,
          NUMERAL_BIT_REV, NUMERAL_BIT_REVERSE,
          numeral_ilog2, numeral_log2,
          NUMERAL_MOD_2EXP, NUMERAL_DIV_2EXP,
          DIVMOD_2EXP, SBIT_def, BITS_def,
          BITV_def, BIT_def, SLICE_def,LSB_def,
          SIGN_EXTEND_def])
 end;

val _ = export_theory();
