(* ========================================================================= *)
(* FILE          : numeral_bitScript.sml                                     *)
(* DESCRIPTION   : Theorems providing numeral based evaluation of            *)
(*                 functions in bitTheory                                    *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2001-2005                                                 *)
(* ========================================================================= *)

open HolKernel Parse boolLib
open BasicProvers metisLib simpLib numSimps numLib
open arithmeticTheory numeralTheory bitTheory

val _ = new_theory "numeral_bit";

infix \\ >- >|
val op \\ = op THEN;
val op >- = op THEN1;
val op >| = op THENL;

(* ------------------------------------------------------------------------- *)

val BIT1n =
   METIS_PROVE [ONE, ADD_ASSOC, BIT1, TIMES2] ``!n. BIT1 n = 2 * n + 1``

val BIT2n =
   METIS_PROVE [ADD_ASSOC,ADD1,ADD,BIT2,TIMES2] ``!n. BIT2 n = 2 * (SUC n)``

val ONE_LT_TWO = METIS_PROVE [ONE, TWO, prim_recTheory.LESS_SUC_REFL] ``1 < 2``

val ONE_LT_TWOEXP =
   METIS_PROVE [EXP_BASE_LT_MONO, EXP, ONE_LT_TWO, prim_recTheory.LESS_0]
     ``!n. 1 < 2 ** SUC n``

val ZERO_LT_TWO = METIS_PROVE [TWO, prim_recTheory.LESS_0] ``0 < 2``

val ZERO_LT_TWOEXP =
   (GEN_ALL o REWRITE_RULE [GSYM TWO] o Q.SPECL [`n`,`1`]) ZERO_LESS_EXP

val DOUBLE_LT_COR =
   METIS_PROVE [DOUBLE_LT, LT_MULT_LCANCEL, ZERO_LT_TWO]
     ``!a b. a < b ==> 2 * a + 1 < 2 * b``

val NUMERAL_MOD_2EXP = Q.prove(
  `(!n. MOD_2EXP 0 n = ZERO) /\
   (!x n. MOD_2EXP x ZERO = ZERO) /\
   (!x n. MOD_2EXP (SUC x) (BIT1 n) = BIT1 (MOD_2EXP x n)) /\
   (!x n. MOD_2EXP (SUC x) (BIT2 n) = numeral$iDUB (MOD_2EXP x (SUC n)))`,
  RW_TAC bool_ss [MOD_2EXP_def, iDUB, GSYM DIV2_def, EXP, MOD_1, GSYM TIMES2,
                  REWRITE_RULE [SYM ALT_ZERO, NUMERAL_DEF, ADD1] numeral_div2]
  THENL [
     REWRITE_TAC [ALT_ZERO],
     METIS_TAC [ALT_ZERO, ZERO_MOD, ZERO_LT_TWOEXP],
     STRIP_ASSUME_TAC (Q.SPEC `x` num_CASES)
     THENL [
        ASM_REWRITE_TAC [EXP, MULT_RIGHT_1, MOD_1]
        \\ SUBST1_TAC (Q.SPEC `n` BIT1n)
        \\ SIMP_TAC bool_ss
             [ONE_LT_TWO, MOD_MULT, Q.SPEC `0` BIT1n,
              ONCE_REWRITE_RULE [GSYM MULT_COMM] MOD_MULT, MULT_0, ADD],
        POP_ASSUM SUBST1_TAC
        \\ SUBST1_TAC (Q.SPEC `n` BIT1n)
        \\ SIMP_TAC bool_ss [Once (GSYM MOD_PLUS), ZERO_LT_TWOEXP, GSYM EXP]
        \\ SIMP_TAC bool_ss
             [Once EXP, GSYM MOD_COMMON_FACTOR, ZERO_LT_TWOEXP, ZERO_LT_TWO]
        \\ SIMP_TAC bool_ss [LESS_MOD, ONE_LT_TWOEXP]
        \\ METIS_TAC
             [BIT1n, DOUBLE_LT_COR, LESS_MOD, EXP, DIVISION, ZERO_LT_TWOEXP]
     ],
     Q.SPEC_THEN `n` SUBST1_TAC BIT2n
     \\ METIS_TAC
          [MOD_COMMON_FACTOR, TWO, prim_recTheory.LESS_0, ZERO_LT_TWOEXP]
  ])

val iMOD_2EXP = new_definition("iMOD_2EXP", ``iMOD_2EXP = MOD_2EXP``)

val BIT1n = REWRITE_RULE [GSYM ADD1] BIT1n

val numeral_imod_2exp = Q.store_thm("numeral_imod_2exp",
  `(!n. iMOD_2EXP 0 n = ZERO) /\
   (!x n. iMOD_2EXP x ZERO = ZERO) /\
   (!x n. iMOD_2EXP (NUMERAL (BIT1 x)) (BIT1 n) =
          BIT1 (iMOD_2EXP (NUMERAL (BIT1 x) - 1) n)) /\
   (!x n. iMOD_2EXP (NUMERAL (BIT2 x)) (BIT1 n) =
          BIT1 (iMOD_2EXP (NUMERAL (BIT1 x)) n)) /\
   (!x n. iMOD_2EXP (NUMERAL (BIT1 x)) (BIT2 n) =
          numeral$iDUB (iMOD_2EXP (NUMERAL (BIT1 x) - 1) (SUC n))) /\
    !x n. iMOD_2EXP (NUMERAL (BIT2 x)) (BIT2 n) =
          numeral$iDUB (iMOD_2EXP (NUMERAL (BIT1 x)) (SUC n))`,
  RW_TAC bool_ss [iMOD_2EXP, NUMERAL_MOD_2EXP]
  \\ SUBST1_TAC (Q.SPEC `BIT1 x` NUMERAL_DEF)
  \\ SUBST1_TAC (Q.SPEC `BIT2 x` NUMERAL_DEF)
  \\ SUBST1_TAC (Q.SPEC `x` BIT1n)
  \\ SUBST1_TAC (Q.SPEC `x` ((GSYM o hd o tl o CONJUNCTS) numeral_suc))
  \\ SIMP_TAC bool_ss [NUMERAL_MOD_2EXP, SUC_SUB1, GSYM BIT1n])

val MOD_2EXP = save_thm("MOD_2EXP",
  CONJ (REWRITE_RULE [ALT_ZERO] (hd (tl (CONJUNCTS NUMERAL_MOD_2EXP))))
       (METIS_PROVE [NUMERAL_DEF, iMOD_2EXP]
         ``!x n. MOD_2EXP x (NUMERAL n) = NUMERAL (iMOD_2EXP x n)``))

val DIV_2EXP = Q.store_thm("DIV_2EXP",
  `!n x. DIV_2EXP n x = FUNPOW DIV2 n x`,
  Induct
  \\ ASM_SIMP_TAC bool_ss
        [DIV_2EXP_def, CONJUNCT1 FUNPOW, FUNPOW_SUC, CONJUNCT1 EXP, DIV_1]
  \\ POP_ASSUM
        (fn th =>
            SIMP_TAC bool_ss
               [GSYM th, EXP_1, ADD1, EXP_ADD, DIV2_def, DIV_2EXP_def,
                DIV_DIV_DIV_MULT, ZERO_LT_TWO, ZERO_LT_TWOEXP]))

(* ------------------------------------------------------------------------- *)

val numeral_mod2 = Q.store_thm("numeral_mod2",
   `(0 MOD 2 = 0) /\
    (!n. NUMERAL (BIT1 n) MOD 2 = 1) /\
    (!n. NUMERAL (BIT2 n) MOD 2 = 0)`,
   SRW_TAC [] []
   >| [`NUMERAL (BIT1 n) = 2 * n + 1`
       by metisLib.METIS_TAC [NUMERAL_DEF, ONE, ADD_ASSOC, BIT1, TIMES2],
       `NUMERAL (BIT2 n) = 2 * (SUC n)`
       by metisLib.METIS_TAC [NUMERAL_DEF, ADD_ASSOC, ADD1, ADD, BIT2, TIMES2]]
   \\ POP_ASSUM SUBST1_TAC
   \\ SRW_TAC [numSimps.MOD_ss] [])

val iDUB_NUMERAL = Q.store_thm("iDUB_NUMERAL",
   `numeral$iDUB (NUMERAL i) = NUMERAL (numeral$iDUB i)`,
   REWRITE_TAC [arithmeticTheory.NUMERAL_DEF])

val BIT_REV_def =
   Prim_rec.new_recursive_definition
     {name = "BIT_REV_def",
      def = ``(BIT_REV 0 x y = y) /\
              (BIT_REV (SUC n) x y =
               BIT_REV n (x DIV 2) (2 * y + SBIT (ODD x) 0))``,
      rec_axiom = prim_recTheory.num_Axiom}

val BIT_R = ``\(x,y). (x DIV 2, 2 * y + SBIT (BIT 0 x) 0)``

val BIT_R_FUNPOW = Q.prove(
   `!n x y.
      FUNPOW ^BIT_R (SUC n) (x,y) =
      (x DIV 2 ** (SUC n),
       2 * (SND (FUNPOW ^BIT_R n (x, y))) + SBIT (BIT n x) 0)`,
   Induct
   >- SIMP_TAC arith_ss [FUNPOW]
   \\ `!x n. BIT 0 (x DIV 2 ** n) = BIT n x`
   by SIMP_TAC std_ss [BIT_def, BITS_THM, BITS_COMP_THM2, DIV_1, SUC_SUB]
   \\ ASM_SIMP_TAC std_ss [FUNPOW_SUC, DIV_DIV_DIV_MULT, ZERO_LT_TWOEXP,
                           (GSYM o ONCE_REWRITE_RULE [MULT_COMM]) EXP])

val BIT_R_BIT_REV = Q.prove(
   `!n a y. SND (FUNPOW ^BIT_R n (a, y)) = BIT_REV n a y`,
   Induct
   >- SIMP_TAC std_ss [FUNPOW, BIT_REV_def]
   \\ ASM_SIMP_TAC std_ss [FUNPOW, BIT_REV_def, GSYM BIT0_ODD])

val BIT_REVERSE_REV = Q.prove(
   `!m n. BIT_REVERSE m n = SND (FUNPOW ^BIT_R m (n, 0))`,
   Induct
   >- SIMP_TAC std_ss [BIT_REVERSE_def, FUNPOW]
   \\ ASM_SIMP_TAC arith_ss [BIT_REVERSE_def, BIT_R_FUNPOW])

val BIT_REVERSE_EVAL = save_thm("BIT_REVERSE_EVAL",
   REWRITE_RULE [BIT_R_BIT_REV] BIT_REVERSE_REV)

(* ------------------------------------------------------------------------- *)

val BIT_MODF_def =
  Prim_rec.new_recursive_definition
     {name = "BIT_MODF_def",
      def = ``(BIT_MODF 0 f x b e y = y) /\
              (BIT_MODF (SUC n) f x b e y =
                 BIT_MODF n f (x DIV 2) (b + 1) (2 * e)
                   (if f b (ODD x) then e + y else y))``,
      rec_axiom = prim_recTheory.num_Axiom}

val BIT_M =
   ``\(y,f,x,b,e).
        (if f b (BIT 0 x) then e + y else y, f, x DIV 2, b + 1, 2 * e)``

val BIT_M_FUNPOW = Q.prove(
   `!n f x b e y. FUNPOW ^BIT_M (SUC n) (y,f,x,b,e) =
        (if f (b + n) (BIT n x)
            then 2 ** n * e + FST (FUNPOW ^BIT_M n (y,f,x,b,e))
         else FST (FUNPOW ^BIT_M n (y,f,x,b,e)),
         f, x DIV 2 ** (SUC n), b + SUC n, 2 ** SUC n * e)`,
   Induct
   >- SIMP_TAC arith_ss [FUNPOW]
   \\ `!x n. BIT 0 (x DIV 2 ** n) = BIT n x`
   by SIMP_TAC std_ss [BIT_def, BITS_THM, BITS_COMP_THM2, DIV_1, SUC_SUB]
   \\ ASM_SIMP_TAC arith_ss
        [FUNPOW_SUC, DIV_DIV_DIV_MULT, ZERO_LT_TWOEXP,
         (GSYM o ONCE_REWRITE_RULE [MULT_COMM]) EXP]
   \\ SIMP_TAC (std_ss++numSimps.ARITH_AC_ss) [EXP])

val BIT_M_BIT_MODF = Q.prove(
   `!n f x b e y. FST (FUNPOW ^BIT_M n (y,f,x,b,e)) = BIT_MODF n f x b e y`,
   Induct
   >- SIMP_TAC std_ss [FUNPOW, BIT_MODF_def]
   \\ ASM_SIMP_TAC std_ss [FUNPOW, BIT_MODF_def, GSYM BIT0_ODD])

val BIT_MODIFY_MODF = Q.prove(
   `!m f n. BIT_MODIFY m f n = FST (FUNPOW ^BIT_M m (0,f,n,0,1))`,
   Induct
   >- SIMP_TAC std_ss [BIT_MODIFY_def, FUNPOW]
   \\ RW_TAC arith_ss [SBIT_def, BIT_MODIFY_def, BIT_M_FUNPOW])

val BIT_MODIFY_EVAL = save_thm("BIT_MODIFY_EVAL",
   REWRITE_RULE [BIT_M_BIT_MODF] BIT_MODIFY_MODF)

(* ------------------------------------------------------------------------- *)

val SUC_RULE = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV

val iBITWISE_def =
   Definition.new_definition("iBITWISE_def", ``iBITWISE = BITWISE``)

val SIMP_BIT1 = (GSYM o SIMP_RULE arith_ss []) BIT1

val iBITWISE = Q.prove(
   `(!opr a b. iBITWISE 0 opr a b = ZERO) /\
    (!x opr a b.
      iBITWISE (SUC x) opr a b =
        let w = iBITWISE x opr (DIV2 a) (DIV2 b) in
        if opr (ODD a) (ODD b) then BIT1 w else numeral$iDUB w)`,
   RW_TAC arith_ss [iBITWISE_def, iDUB, SIMP_BIT1, SBIT_def, EXP,
                    BIT0_ODD, GSYM DIV2_def, BITWISE_EVAL, LET_THM]
   \\ REWRITE_TAC [BITWISE_def, ALT_ZERO])

val iBITWISE = save_thm("iBITWISE", SUC_RULE iBITWISE)

val NUMERAL_BITWISE = Q.store_thm("NUMERAL_BITWISE",
   `(!x f a. BITWISE x f 0 0 = NUMERAL (iBITWISE x f 0 0)) /\
    (!x f a. BITWISE x f (NUMERAL a) 0 =
             NUMERAL (iBITWISE x f (NUMERAL a) 0)) /\
    (!x f b. BITWISE x f 0 (NUMERAL b) =
             NUMERAL (iBITWISE x f 0 (NUMERAL b))) /\
     !x f a b. BITWISE x f (NUMERAL a) (NUMERAL b) =
               NUMERAL (iBITWISE x f (NUMERAL a) (NUMERAL b))`,
   REWRITE_TAC [iBITWISE_def, NUMERAL_DEF])

val NUMERAL_BIT_REV = Q.prove(
   `(!x y. BIT_REV 0 x y = y) /\
    (!n y. BIT_REV (SUC n) 0 y = BIT_REV n 0 (numeral$iDUB y)) /\
    (!n x y. BIT_REV (SUC n) (NUMERAL x) y =
             BIT_REV n (DIV2 (NUMERAL x))
                (if ODD x then BIT1 y else numeral$iDUB y))`,
   RW_TAC bool_ss [BIT_REV_def, SBIT_def, NUMERAL_DEF, DIV2_def,
                   ADD, ADD_0, BIT2, BIT1, iDUB, ALT_ZERO]
   \\ FULL_SIMP_TAC arith_ss [])

val NUMERAL_BIT_REV = save_thm("NUMERAL_BIT_REV", SUC_RULE NUMERAL_BIT_REV)

val NUMERAL_BIT_REVERSE = Q.store_thm("NUMERAL_BIT_REVERSE",
   `(!m. BIT_REVERSE (NUMERAL m) 0 = NUMERAL (BIT_REV (NUMERAL m) 0 ZERO)) /\
     !n m. BIT_REVERSE (NUMERAL m) (NUMERAL n) =
           NUMERAL (BIT_REV (NUMERAL m) (NUMERAL n) ZERO)`,
   SIMP_TAC bool_ss [NUMERAL_DEF, ALT_ZERO, BIT_REVERSE_EVAL])

val NUMERAL_BIT_MODF = Q.prove(
   `(!f x b e y. BIT_MODF 0 f x b e y = y) /\
    (!n f b e y.
       BIT_MODF (SUC n) f 0 b (NUMERAL e) y =
       BIT_MODF n f 0 (b + 1) (NUMERAL (numeral$iDUB e))
          (if f b F then (NUMERAL e) + y else y)) /\
    (!n f x b e y.
       BIT_MODF (SUC n) f (NUMERAL x) b (NUMERAL e) y =
       BIT_MODF n f (DIV2 (NUMERAL x)) (b + 1) (NUMERAL (numeral$iDUB e))
          (if f b (ODD x) then (NUMERAL e) + y else y))`,
   RW_TAC bool_ss [BIT_MODF_def, SBIT_def, NUMERAL_DEF, DIV2_def,
                   ADD, ADD_0, BIT2, BIT1, iDUB, ALT_ZERO]
   \\ FULL_SIMP_TAC arith_ss [])

val NUMERAL_BIT_MODF = save_thm("NUMERAL_BIT_MODF", SUC_RULE NUMERAL_BIT_MODF)

val NUMERAL_BIT_MODIFY = Q.store_thm("NUMERAL_BIT_MODIFY",
  `(!m f. BIT_MODIFY (NUMERAL m) f 0 = BIT_MODF (NUMERAL m) f 0 0 1 0) /\
    !m f n. BIT_MODIFY (NUMERAL m) f (NUMERAL n) =
            BIT_MODF (NUMERAL m) f (NUMERAL n) 0 1 0`,
  SIMP_TAC bool_ss [NUMERAL_DEF, ALT_ZERO, BIT_MODIFY_EVAL])

(* ------------------------------------------------------------------------- *)

val iSUC_def = Definition.new_definition ("iSUC",``iSUC = SUC``)

val iDIV2_def = Definition.new_definition ("iDIV2",``iDIV2 = DIV2``)

val SFUNPOW_def =
  Prim_rec.new_recursive_definition
    {name = "SFUNPOW_def",
     def = ``(SFUNPOW f 0 x = x) /\
             (SFUNPOW f (SUC n) x = if x = 0n then 0n else SFUNPOW f n (f x))``,
     rec_axiom = prim_recTheory.num_Axiom}

val FDUB_def =
   Prim_rec.new_recursive_definition
      {name = "FDUB_def",
       def = ``(FDUB f 0 = 0n) /\
               (FDUB f (SUC n) = f (f (SUC n)))``,
      rec_axiom = prim_recTheory.num_Axiom}

val FDUB_lem = Q.prove(
   `!f. (f 0 = 0n) ==> (FDUB f = (\x.f (f x)))`,
   REWRITE_TAC [FUN_EQ_THM]
   \\ GEN_TAC
   \\ DISCH_TAC
   \\ BETA_TAC
   \\ Cases
   \\ ASM_REWRITE_TAC [FDUB_def])

val SFUNPOW_strict = Q.prove(
   `!n f x. SFUNPOW f n 0 = 0`,
   Cases \\ REWRITE_TAC [SFUNPOW_def])

val SFUNPOW_BIT1_lem = Q.prove(
   `!n f x.
      (f 0 = 0) ==>
      (SFUNPOW f (NUMERAL (BIT1 n)) x = SFUNPOW (FDUB f) n (f x))`,
   REWRITE_TAC [NUMERAL_DEF, BIT1, ADD_CLAUSES]
   \\ Induct
   \\ REPEAT STRIP_TAC
   \\ REWRITE_TAC [NUMERAL_DEF, BIT1, ADD_CLAUSES]
   >- (IMP_RES_TAC FDUB_lem \\ ASM_REWRITE_TAC [SFUNPOW_def] \\ PROVE_TAC [])
   \\ ONCE_REWRITE_TAC [SFUNPOW_def]
   \\ ONCE_REWRITE_TAC [SFUNPOW_def]
   \\ RES_TAC
   \\ RW_TAC std_ss []
   \\ IMP_RES_TAC FDUB_lem
   \\ PROVE_TAC [])

val SFUNPOW_BIT2_lem = Q.prove(
   `!n f x.
      (f 0 = 0) ==>
      (SFUNPOW f (NUMERAL (BIT2 n)) x = SFUNPOW (FDUB f) n (f (f x)))`,
   `!n. NUMERAL (BIT2 n) = SUC (NUMERAL (BIT1 n))`
   by REWRITE_TAC [NUMERAL_DEF, BIT1, BIT2, ADD_CLAUSES]
   \\ REPEAT STRIP_TAC
   \\ IMP_RES_TAC SFUNPOW_BIT1_lem
   \\ ASM_REWRITE_TAC [SFUNPOW_def]
   \\ RW_TAC std_ss [SFUNPOW_strict])

val NUMERAL_SFUNPOW = Q.prove(
  `!f. (f 0 = 0) ==>
       (!x. SFUNPOW f 0 x = x) /\
       (!y. SFUNPOW f y 0 = 0) /\
       (!n x. SFUNPOW f (NUMERAL (BIT1 n)) x =
              SFUNPOW (FDUB f) (NUMERAL n) (f x)) /\
       (!n x. SFUNPOW f (NUMERAL (BIT2 n)) x =
              SFUNPOW (FDUB f) (NUMERAL n) (f (f x)))`,
   REPEAT STRIP_TAC
   \\ MAP_EVERY IMP_RES_TAC [SFUNPOW_BIT1_lem, SFUNPOW_BIT2_lem]
   \\ ASM_REWRITE_TAC [SFUNPOW_strict, SFUNPOW_def, NUMERAL_DEF])

val NUMERAL_TIMES_2EXP = Q.store_thm("NUMERAL_TIMES_2EXP",
   `(!n. TIMES_2EXP n 0 = 0) /\
    (!n x. TIMES_2EXP n (NUMERAL x) = NUMERAL (SFUNPOW numeral$iDUB n x))`,
   CONJ_TAC
   \\ REWRITE_TAC [TIMES_2EXP_def, MULT_CLAUSES]
   \\ Induct
   \\ REWRITE_TAC [EXP, SFUNPOW_def, MULT_CLAUSES, MULT_ASSOC]
   \\ POP_ASSUM (ASSUME_TAC o GSYM)
   \\ RW_TAC std_ss []
   \\ ASM_REWRITE_TAC [NUMERAL_DEF, BIT1, BIT2, iDUB, ALT_ZERO, ADD_CLAUSES]
   \\ RW_TAC arith_ss [])

val NUMERAL_iDIV2 = Q.store_thm("NUMERAL_iDIV2",
   `(iDIV2 ZERO = ZERO) /\
    (iDIV2 (iSUC ZERO) = ZERO) /\
    (iDIV2 (BIT1 n) = n) /\
    (iDIV2 (iSUC (BIT1 n)) = iSUC n) /\
    (iDIV2 (BIT2 n) = iSUC n) /\
    (iDIV2 (iSUC (BIT2 n)) = iSUC n) /\
    (NUMERAL (iSUC n) = NUMERAL (SUC n))`,
   REWRITE_TAC [ALT_ZERO, BIT1, BIT2, iDIV2_def, iSUC_def, ADD_CLAUSES]
   \\ REWRITE_TAC [DIV2_def, GSYM TIMES2]
   \\ `0 < 2 /\ 1 < 2` by DECIDE_TAC
   \\ MAP_EVERY IMP_RES_TAC
        [ZERO_DIV, ADD_DIV_RWT, DIV_LESS,
         LESS_DIV_EQ_ZERO, ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
   \\ RULE_ASSUM_TAC (REWRITE_RULE [GSYM EVEN_MOD2])
   \\ RW_TAC arith_ss [ADD1, EVEN_DOUBLE])

val NUMERAL_DIV_2EXP = Q.store_thm("NUMERAL_DIV_2EXP",
   `(!n. DIV_2EXP n 0 = 0) /\
    (!n x. DIV_2EXP n (NUMERAL x) = NUMERAL (SFUNPOW iDIV2 n x))`,
   CONJ_TAC
   \\ REWRITE_TAC [DIV_2EXP_def]
   >- (STRIP_TAC \\ MATCH_MP_TAC ZERO_DIV \\ RW_TAC std_ss [ZERO_LT_TWOEXP])
   \\ Induct
   \\ REWRITE_TAC [EXP, SFUNPOW_def, DIV_1]
   \\ `!x. NUMERAL x DIV 2 = NUMERAL (x DIV 2)` by REWRITE_TAC [NUMERAL_DEF]
   \\ RW_TAC arith_ss
         [ZERO_LT_TWOEXP, GSYM DIV_DIV_DIV_MULT, SFUNPOW_strict, iDIV2_def,
          DIV2_def])

val NUMERAL_SFUNPOW_iDIV2 = save_thm("NUMERAL_SFUNPOW_iDIV2",
   MATCH_MP (SPEC_ALL NUMERAL_SFUNPOW)
      (Q.prove(`iDIV2 0 = 0`, RW_TAC arith_ss [iDIV2_def, DIV2_def])))

val NUMERAL_SFUNPOW_iDUB = save_thm("NUMERAL_SFUNPOW_iDUB",
   MATCH_MP (SPEC_ALL NUMERAL_SFUNPOW)
      (Q.prove(`numeral$iDUB 0 = 0`, RW_TAC arith_ss [iDUB])))

val NUMERAL_SFUNPOW_FDUB = save_thm("NUMERAL_SFUNPOW_FDUB",
   GEN_ALL (MATCH_MP (SPEC_ALL NUMERAL_SFUNPOW)
                     (SPEC_ALL (CONJUNCT1 FDUB_def))))

val FDUB_iDIV2 = Q.store_thm("FDUB_iDIV2",
   `!x. FDUB iDIV2 x = iDIV2 (iDIV2 x)`,
   Cases \\ RW_TAC arith_ss [FDUB_def, iDIV2_def, DIV2_def])

val FDUB_iDUB = Q.store_thm("FDUB_iDUB",
   `!x. FDUB numeral$iDUB x = numeral$iDUB (numeral$iDUB x)`,
   Cases \\ RW_TAC arith_ss [FDUB_def, iDUB])

val FDUB_FDUB = Q.store_thm("FDUB_FDUB",
   `(FDUB (FDUB f) ZERO = ZERO) /\
    (!x. FDUB (FDUB f) (iSUC x) = FDUB f (FDUB f (iSUC x))) /\
    (!x. FDUB (FDUB f) (BIT1 x) = FDUB f (FDUB f (BIT1 x))) /\
    (!x. FDUB (FDUB f) (BIT2 x) = FDUB f (FDUB f (BIT2 x)))`,
   REWRITE_TAC [BIT1, BIT2, iSUC_def, FDUB_def, ALT_ZERO, ADD_CLAUSES])

(* ------------------------------------------------------------------------- *)

val LOG_compute = Q.store_thm("LOG_compute",
   `!m n. LOG m n =
          if m < 2 \/ (n = 0) then
            FAIL LOG ^(mk_var("base < 2 or n = 0", bool)) m n
          else
            if n < m then
              0
            else
              SUC (LOG m (n DIV m))`,
   SRW_TAC [ARITH_ss] [logrootTheory.LOG_RWT, combinTheory.FAIL_THM])

val iLOG2_def =
   Definition.new_definition("iLOG2_def", ``iLOG2 n = LOG2 (n + 1)``)

val LOG2_1 = (SIMP_RULE arith_ss [] o Q.SPECL [`1`,`0`]) LOG2_UNIQUE

val numeral_ilog2 = Q.store_thm("numeral_ilog2",
   `(iLOG2 ZERO = 0) /\
    (!n. iLOG2 (BIT1 n) = 1 + iLOG2 n) /\
    (!n. iLOG2 (BIT2 n) = 1 + iLOG2 n)`,
   RW_TAC bool_ss [ALT_ZERO, NUMERAL_DEF, BIT1, BIT2, iLOG2_def]
   \\ SIMP_TAC arith_ss [LOG2_1]
   >| [
      MATCH_MP_TAC
         ((SIMP_RULE arith_ss [] o Q.SPECL [`2 * n + 2`, `LOG2 (n + 1) + 1`])
             LOG2_UNIQUE)
      \\ SIMP_TAC arith_ss [EXP_ADD, LOG2_def]
      \\ SIMP_TAC arith_ss
            [GSYM ADD1, EXP, logrootTheory.LOG,
             DECIDE ``(2 * n + 2 = (n + 1) * 2) /\
                      (2 * a < 4 * b = a < 2 * b)``]
      \\ SIMP_TAC arith_ss [GSYM EXP, logrootTheory.LOG],
      MATCH_MP_TAC
         ((SIMP_RULE arith_ss [] o Q.SPECL [`2 * n + 3`, `LOG2 (n + 1) + 1`])
             LOG2_UNIQUE)
      \\ SIMP_TAC arith_ss [EXP_ADD, LOG2_def]
      \\ SIMP_TAC arith_ss
            [GSYM ADD1, EXP, logrootTheory.LOG,
             DECIDE ``(2 * n + 3 = 2 * (n + 1) + 1)``,
             DECIDE ``a <= b ==> 2 * a <= SUC (2 * b)``]
      \\ SIMP_TAC arith_ss
            [DECIDE ``a < 2 * b ==> SUC (2 * a) < 4 * b``,
             (Once o GSYM) EXP, logrootTheory.LOG]
   ])

val numeral_log2 = Q.store_thm("numeral_log2",
   `(!n. LOG2 (NUMERAL (BIT1 n)) = iLOG2 (numeral$iDUB n)) /\
    (!n. LOG2 (NUMERAL (BIT2 n)) = iLOG2 (BIT1 n))`,
   RW_TAC bool_ss [ALT_ZERO, NUMERAL_DEF, BIT1, BIT2, iLOG2_def,
                   numeralTheory.iDUB]
   \\ SIMP_TAC arith_ss [])

(* ------------------------------------------------------------------------- *)

val MOD_2EXP_EQ = Q.store_thm("MOD_2EXP_EQ",
   `(!a b. MOD_2EXP_EQ 0 a b = T) /\
    (!n a b.
       MOD_2EXP_EQ (SUC n) a b =
       (ODD a = ODD b) /\ MOD_2EXP_EQ n (DIV2 a) (DIV2 b)) /\
    (!n a. MOD_2EXP_EQ n a a = T)`,
   SRW_TAC [] [MOD_2EXP_EQ_def, MOD_2EXP_def, GSYM BITS_ZERO3]
   \\ Cases_on `n`
   \\ FULL_SIMP_TAC std_ss [GSYM BITS_ZERO3, GSYM BIT0_ODD,
                            GSYM BIT_BITS_THM, BIT_DIV2, DIV2_def]
   \\ EQ_TAC
   \\ RW_TAC arith_ss []
   \\ Cases_on `x`
   \\ RW_TAC arith_ss [])

val lem = Q.prove(
   `!n. BITS n 0 (2 ** SUC n - 1) = 2 ** SUC n - 1`,
   STRIP_TAC
   \\ MATCH_MP_TAC BITS_ZEROL
   \\ SIMP_TAC std_ss [ZERO_LT_TWOEXP])

val MOD_2EXP_MAX = Q.store_thm("MOD_2EXP_MAX",
   `(!a. MOD_2EXP_MAX 0 a = T) /\
    (!n a. MOD_2EXP_MAX (SUC n) a = ODD a /\ MOD_2EXP_MAX n (DIV2 a))`,
    SRW_TAC [] [MOD_2EXP_MAX_def, MOD_2EXP_def, GSYM BITS_ZERO3]
    \\ Cases_on `n`
    >- SIMP_TAC std_ss [SYM BIT0_ODD, BIT_def]
    \\ ONCE_REWRITE_TAC [GSYM lem]
    \\ SIMP_TAC std_ss
          [GSYM BITS_ZERO3, SYM BIT0_ODD, GSYM BIT_BITS_THM, BIT_DIV2, DIV2_def]
    \\ EQ_TAC
    \\ RW_TAC arith_ss [BIT_EXP_SUB1]
    \\ Cases_on `x` 
    \\ RW_TAC arith_ss [])

(* ------------------------------------------------------------------------- *)

val LEAST_BIT_INTRO =
   (SIMP_RULE (srw_ss()) [] o Q.SPEC `\i. BIT i n`)  whileTheory.LEAST_INTRO

val LOWEST_SET_BIT = Q.store_thm("LOWEST_SET_BIT",
   `!n. ~(n = 0) ==>
        (LOWEST_SET_BIT n = if ODD n then 0 else 1 + LOWEST_SET_BIT (DIV2 n))`,
   SRW_TAC [ARITH_ss] [LOWEST_SET_BIT_def, DIV2_def, ADD1]
   \\ MATCH_MP_TAC LEAST_THM
   \\ SRW_TAC [] [BIT0_ODD]
   >| [
      Cases_on `(LEAST i. BIT i (n DIV 2)) = 0`
      >- FULL_SIMP_TAC (srw_ss()) [DECIDE ``m < 1 ==> (m = 0)``, BIT0_ODD]
      \\ IMP_RES_TAC (DECIDE ``~(a = 0) /\ m < a + 1 ==> (m - 1 < a)``)
      \\ IMP_RES_TAC whileTheory.LESS_LEAST
      \\ FULL_SIMP_TAC (srw_ss()) [BIT_DIV2]
      \\ Cases_on `m = 0`
      \\ FULL_SIMP_TAC (srw_ss())
           [BIT0_ODD, DECIDE ``~(m = 0) ==> (SUC (m - 1) = m)``],
      SRW_TAC [] [GSYM ADD1, GSYM BIT_DIV2]
      \\ MATCH_MP_TAC LEAST_BIT_INTRO
      \\ `~(n DIV 2 = 0)`
      by (Cases_on `n = 1`
          \\ FULL_SIMP_TAC arith_ss
                [(SIMP_RULE (srw_ss()) [DECIDE ``0 < n = ~(n = 0)``] o
                  Q.SPECL [`0`,`n`,`2`]) X_LT_DIV])
      \\ METIS_TAC [BIT_LOG2]
   ])

val LOWEST_SET_BIT_compute = save_thm("LOWEST_SET_BIT_compute",
   let
      open numeralTheory
      val rule = (GEN_ALL o SIMP_RULE (srw_ss())
                   [DECIDE ``1 + n = SUC n``, numeral_eq, numeral_distrib,
                     numeral_evenodd, numeral_div2])
   in
      CONJ ((rule o Q.SPEC `NUMERAL (BIT2 n)`) LOWEST_SET_BIT)
           ((rule o Q.SPEC `NUMERAL (BIT1 n)`) LOWEST_SET_BIT)
   end)

(* ------------------------------------------------------------------------- *)

val () =
   List.app (fn s => remove_ovl_mapping s {Name = s, Thy = "numeral_bit"})
            ["iBITWISE", "iSUC", "iDIV2", "iLOG2", "iMOD_2EXP"]

val _ = export_theory()
