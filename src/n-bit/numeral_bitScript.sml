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

val iBITWISE_def =
  Definition.new_definition("iBITWISE_def", ``iBITWISE = BITWISE``);

val SIMP_BIT1 = (GSYM o SIMP_RULE arith_ss []) BIT1;

val iBITWISE = prove(
  `(!opr a b. iBITWISE 0 opr a b = ZERO) /\
   (!x opr a b.
     iBITWISE (SUC x) opr a b =
       let w = iBITWISE x opr (DIV2 a) (DIV2 b) in
       if opr (ODD a) (ODD b) then BIT1 w else numeral$iDUB w)`,
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

val NUMERAL_BIT_REV = prove(
  `(!x y. BIT_REV 0 x y = y) /\
   (!n y. BIT_REV (SUC n) 0 y = BIT_REV n 0 (numeral$iDUB y)) /\
   (!n x y. BIT_REV (SUC n) (NUMERAL x) y =
      BIT_REV n (DIV2 (NUMERAL x)) (if ODD x then BIT1 y
                                    else numeral$iDUB y))`,
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
      BIT_MODF n f 0 (b + 1) (NUMERAL (numeral$iDUB e))
              (if f b F then (NUMERAL e) + y else y)) /\
   (!n f x b e y. BIT_MODF (SUC n) f (NUMERAL x) b (NUMERAL e) y =
      BIT_MODF n f (DIV2 (NUMERAL x)) (b + 1) (NUMERAL (numeral$iDUB e))
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

val TIMES_2EXP_lem = prove(
  `!n. FUNPOW numeral$iDUB n 1 = 2 ** n`,
  Induct \\ ASM_SIMP_TAC arith_ss
    [EXP,CONJUNCT1 FUNPOW,FUNPOW_SUC,iDUB,GSYM TIMES2]);

val NUMERAL_TIMES_2EXP = store_thm("NUMERAL_TIMES_2EXP",
  `(!n. TIMES_2EXP n 0 = 0) /\ (!x. TIMES_2EXP 0 x = x) /\
  !x n. TIMES_2EXP (NUMERAL x) (NUMERAL n) =
     (NUMERAL n) * NUMERAL (FUNPOW numeral$iDUB (NUMERAL x) (BIT1 ZERO))`,
  `BIT1 ZERO = 1` by REWRITE_TAC [NUMERAL_DEF,BIT1,ALT_ZERO]
    \\ POP_ASSUM SUBST1_TAC
    \\ REWRITE_TAC [TIMES_2EXP_def,TIMES_2EXP_lem,NUMERAL_DEF]
    \\ SIMP_TAC std_ss [EXP]);

val DIV_2EXP = prove(
  `(!n. DIV_2EXP 0 n = n) /\
   (!x. DIV_2EXP x 0 = 0) /\
   (!x n. DIV_2EXP (SUC x) (NUMERAL n) =
            DIV_2EXP x (DIV2 (NUMERAL n)))`,
  RW_TAC arith_ss [DIV_2EXP_def,DIV2_def,EXP,ZERO_DIV,
    DIV_DIV_DIV_MULT,ZERO_LT_TWOEXP]);

val NUMERAL_DIV_2EXP = save_thm("NUMERAL_DIV_2EXP", SUC_RULE DIV_2EXP);

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
  `(!n. LOG2 (NUMERAL (BIT1 n)) = iLOG2 (numeral$iDUB n)) /\
   (!n. LOG2 (NUMERAL (BIT2 n)) = iLOG2 (BIT1 n))`,
  RW_TAC bool_ss [ALT_ZERO,NUMERAL_DEF,BIT1,BIT2,iLOG2_def,numeralTheory.iDUB]
    \\ SIMP_TAC arith_ss []);

(* ------------------------------------------------------------------------- *)

val PRE = prim_recTheory.PRE;
val NOT_SUC = numTheory.NOT_SUC;

val NUMERAL_1 = prove(
  `!n. (NUMERAL (BIT1 n) = 1) = (n = 0)`,
  REWRITE_TAC [GSYM (REWRITE_CONV [GSYM ALT_ZERO] ``NUMERAL (BIT1 0)``)]
    \\ SIMP_TAC bool_ss [BIT1, NUMERAL_DEF]
    \\ DECIDE_TAC);

val NUMERAL_1b = prove(
  `!n. ~(NUMERAL (BIT2 n) = 1)`,
  REWRITE_TAC [GSYM (REWRITE_CONV [GSYM ALT_ZERO] ``NUMERAL (BIT1 0)``)]
    \\ SIMP_TAC bool_ss [BIT1, BIT2, NUMERAL_DEF]
    \\ DECIDE_TAC);

val iDUB_SUC = prove(`!n. numeral$iDUB (SUC n) = BIT2 n`,
  SIMP_TAC bool_ss [iDUB, BIT2, ADD1] \\ DECIDE_TAC);

val DIV2_BIT1_SUC = prove(
  `!n. DIV2 (NUMERAL (BIT1 (SUC n))) = n + 1`,
  REWRITE_TAC [DIV2_def]
    \\ GEN_REWRITE_TAC (DEPTH_CONV o RATOR_CONV o RAND_CONV) empty_rewrites
         [BIT1, SPEC `BIT1 (SUC n)` NUMERAL_DEF]
    \\ SIMP_TAC arith_ss [ADD1, ONCE_REWRITE_RULE [MULT_COMM] ADD_DIV_ADD_DIV]);

val LOG2_compute = prove(
  `!n. LOG2 n =
         if n = 0 then
           FAIL LOG2 ^(mk_var("undefined",bool)) n
         else
           if n = 1 then
             0
           else
             1 + LOG2 (DIV2 n)`,
  Cases \\ REWRITE_TAC [NOT_SUC, combinTheory.FAIL_THM]
    \\ SPEC_TAC (`n'`,`n`) \\ CONV_TAC numLib.SUC_TO_NUMERAL_DEFN_CONV
    \\ STRIP_TAC
    << [
       REWRITE_TAC [NUMERAL_1] \\ Cases \\ RW_TAC arith_ss [numeral_log2]
         << [PROVE_TAC [iDUB_removal, numeral_ilog2, ALT_ZERO],
             REWRITE_TAC [iDUB_SUC, DIV2_BIT1_SUC, numeral_ilog2]
               \\ SIMP_TAC arith_ss [iLOG2_def]],
       REWRITE_TAC [NUMERAL_1b, numeral_div2, numeral_ilog2, numeral_log2,
                    NUMERAL_DEF, iLOG2_def, ADD1]]);

val BITWISE_compute = prove(
  `!n opr a b.
      BITWISE n opr a b =
        if n = 0 then 0 else
          2 * BITWISE (PRE n) opr (DIV2 a) (DIV2 b) +
          (if opr (ODD a) (ODD b) then 1 else 0)`,
  Cases >> REWRITE_TAC [CONJUNCT1 BITWISE_def]
    \\ REWRITE_TAC
         [DIV2_def, NOT_SUC, PRE, EXP, BITWISE_EVAL, LSB_ODD, SBIT_def]);

val BIT_MODF_compute = prove(
  `!n f x b e y.
      BIT_MODF n f x b e y =
        if n = 0 then y else
          BIT_MODF (PRE n) f (DIV2 x) (b + 1) (2 * e)
           (if f b (ODD x) then e + y else y)`,
  Cases \\ REWRITE_TAC [DIV2_def, NOT_SUC, PRE, BIT_MODF_def]);

val BIT_REV_compute = prove(
  `!n x y.
      BIT_REV n x y =
        if n = 0 then y else
          BIT_REV (PRE n) (DIV2 x) (2 * y + (if ODD x then 1 else 0))`,
  Cases \\ REWRITE_TAC [DIV2_def, NOT_SUC, PRE, BIT_REV_def, EXP, SBIT_def]);

val TIMES_2EXP_compute = prove(
  `!n x. TIMES_2EXP n x = if x = 0 then 0 else x * FUNPOW numeral$iDUB n 1`,
  RW_TAC bool_ss
         [MULT, REWRITE_RULE [NUMERAL_DEF] NUMERAL_TIMES_2EXP,CONJUNCT1 FUNPOW]
    \\ PROVE_TAC [NUMERAL_DEF]);

val TIMES_2EXP1 =
 (GSYM o REWRITE_RULE [arithmeticTheory.MULT_LEFT_1] o
  Q.SPECL [`x`,`1`]) bitTheory.TIMES_2EXP_def;

val _ =
 let open EmitML
 in emitML (!Globals.emitMLDir)
   ("bit",
     MLSIG  "type num = numML.num" :: OPEN ["num"]
     ::
     map (DEFN o PURE_REWRITE_RULE [TIMES_2EXP1, arithmeticTheory.NUMERAL_DEF])
         [TIMES_2EXP_compute, BITWISE_compute,
          BIT_MODF_compute, BIT_MODIFY_EVAL,
          BIT_REV_compute, BIT_REVERSE_EVAL,
          LOG2_compute, DIVMOD_2EXP, SBIT_def, BITS_def,
          BITV_def, BIT_def, SLICE_def,LSB_def, SIGN_EXTEND_def])
 end;

val _ = export_theory();
