(* app load ["bossLib"]; *)
open HolKernel boolLib Parse Q bossLib simpLib numLib
     pairTheory numeralTheory arithmeticTheory prim_recTheory;

infix 8 by;
infix THEN THENC THENL ++;
 

(* -------------------------------------------------------- *)

val _ = new_theory "bits";

(* -------------------------------------------------------- *)

val DIV2_def        = Define `DIV2 n = n DIV 2`;

val TIMES_2EXP_def  = Define `TIMES_2EXP x n = n * 2 EXP x`;

val DIV_2EXP_def    = Define `DIV_2EXP x n = n DIV 2 EXP x`;

val MOD_2EXP_def    = Define `MOD_2EXP x n = n MOD 2 EXP x`;

val DIVMOD_2EXP_def = Define `DIVMOD_2EXP x n = (n DIV 2 EXP x,n MOD 2 EXP x)`;
 
val SET_def         = Define `SET b n = if b then 2 EXP n else 0`;
 
val BITS_def        = Define `BITS h l n = MOD_2EXP (SUC h-l) (DIV_2EXP l n)`;
 
val BIT_def         = Define `BIT b n = (BITS b b n = 1)`;
 
val SLICE_def       = Define `SLICE h l n = MOD_2EXP (SUC h) n - MOD_2EXP l n`;
 
val LSB_def         = Define`LSB = BIT 0`;

val BITWISE_def = 
 Define
   `(BITWISE 0 op x y = 0) 
 /\ (BITWISE (SUC n) op x y = 
       let r = (BITWISE n op (x DIV 2) (y DIV 2)) 
       in if op (LSB x) (LSB y) then r + r + 1 else r + r)`;

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val ZERO_LT_TWOEXP = save_thm("ZERO_LT_TWOEXP",
  GEN_ALL (REDUCE_RULE (Q.SPECL [`n`,`1`] ZERO_LESS_EXP))
);

val BITS_THM = save_thm("BITS_THM",
   REWRITE_RULE [DIV_2EXP_def,MOD_2EXP_def] BITS_def
);

val BITSLT_THM = Q.store_thm("BITSLT_THM",
  `!h l n. BITS h l n < 2 EXP (SUC h-l)`,
  RW_TAC std_ss [BITS_THM,ZERO_LT_TWOEXP,DIVISION]
);

val DIV_MULT_LEM = Q.store_thm("DIV_MULT_LEM",
  `!m n. 0 < n ==> m DIV n * n <= m`,
  RW_TAC arith_ss [LESS_EQ_EXISTS]
    THEN Q.EXISTS_TAC `m MOD n`
    THEN PROVE_TAC [DIVISION,ADD_COMM]
);
 
val DIV_MULT_LESS_EQ = 
  GEN_ALL (SIMP_RULE std_ss [ZERO_LT_TWOEXP] 
             (Q.SPECL [`n`,`2 EXP x`] DIV_MULT_LEM));

val MOD_2EXP_LEM = Q.store_thm("MOD_2EXP_LEM",
  `!n x. n MOD 2 EXP x = n - n DIV 2 EXP x * 2 EXP x`,
  REPEAT STRIP_TAC
    THEN ASSUME_TAC (Q.SPECL [`x`,`n`] DIV_MULT_LESS_EQ)
    THEN RW_TAC std_ss [GSYM ADD_EQ_SUB]
    THEN PROVE_TAC [ZERO_LT_TWOEXP,ADD_COMM,DIVISION]
);
 
val DIV_MULT_LEM2 = prove(
  `!a b p. a DIV 2 EXP (b + p) * 2 EXP (p + b) <= a DIV 2 EXP b * 2 EXP b`,
  REPEAT STRIP_TAC
    THEN ASSUME_TAC (SIMP_RULE std_ss [ZERO_LT_TWOEXP] 
                      (SPECL [`a DIV 2 EXP b`,`2 EXP p`] DIV_MULT_LEM))
    THEN ASM_SIMP_TAC std_ss [EXP_ADD,MULT_ASSOC,GSYM DIV_DIV_DIV_MULT,
                              ZERO_LT_TWOEXP,LESS_MONO_MULT]
);
 
val MOD_EXP_ADD = prove(
  `!a b p. a MOD 2 EXP (b + p) 
               = 
           a MOD 2 EXP b + (a DIV 2 EXP b) MOD 2 EXP p * 2 EXP b`,
 REPEAT STRIP_TAC
  THEN SIMP_TAC std_ss [MOD_2EXP_LEM,RIGHT_SUB_DISTRIB,DIV_DIV_DIV_MULT,
                        ZERO_LT_TWOEXP,GSYM MULT_ASSOC,GSYM EXP_ADD]
  THEN ASSUME_TAC (GSYM (
        SPECL [`a DIV 2 EXP (b + p) * 2 EXP (p + b)`,
               `a DIV 2 EXP b * 2 EXP b`] LESS_EQ_ADD_SUB))
  THEN ASM_SIMP_TAC std_ss [DIV_MULT_LEM2,DIV_MULT_LEM,ZERO_LT_TWOEXP,SUB_ADD]
  THEN PROVE_TAC [ADD_COMM]);
 
val DIV_MOD_MOD_DIV = prove(
  `!a b p. (a DIV 2 EXP b) MOD 2 EXP p = a MOD 2 EXP (b + p) DIV 2 EXP b`,
  REPEAT STRIP_TAC
    THEN SIMP_TAC std_ss [MOD_EXP_ADD]
    THEN ONCE_REWRITE_TAC [ADD_COMM]
    THEN SIMP_TAC arith_ss [ADD_DIV_ADD_DIV,ZERO_LT_TWOEXP,LESS_DIV_EQ_ZERO,
                 SIMP_RULE std_ss [ZERO_LT_TWOEXP] (SPEC `2 EXP b` DIVISION)]
);

 
val DIV_MOD_MOD_DIV2 = prove(
  `!a b c. (a DIV 2 EXP b) MOD 2 EXP (c - b) = (a MOD 2 EXP c) DIV 2 EXP b`,
  REPEAT STRIP_TAC
    THEN Cases_on `c <= b`
    THENL [
       `c - b = 0` by PROVE_TAC [SUB_EQ_0]
          THEN RW_TAC arith_ss [REDUCE_RULE MOD_ONE]
          THEN ASSUME_TAC (SPEC `a` 
              (SIMP_RULE std_ss [ZERO_LT_TWOEXP] (SPEC `2 EXP c` DIVISION)))
          THEN FULL_SIMP_TAC std_ss []
          THEN IMP_RES_TAC LESS_EQUAL_ADD
          THEN POP_ASSUM (fn th => REWRITE_TAC [th])
          THEN ASSUME_TAC (GSYM (SIMP_RULE std_ss [ZERO_LT_TWOEXP]
                           (SPECL [`2 EXP c`,`2 EXP p`] DIV_DIV_DIV_MULT)))
          THEN ASM_SIMP_TAC std_ss 
                   [EXP_ADD,LESS_DIV_EQ_ZERO,ZERO_DIV,ZERO_LT_TWOEXP],
       RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS_EQUAL])
          THEN IMP_RES_TAC LESS_ADD
          THEN POP_ASSUM (fn th => REWRITE_TAC [SYM th])
          THEN SIMP_TAC arith_ss [DIV_MOD_MOD_DIV]
    ]
);

val BITS2_THM = store_thm("BITS2_THM",
  `!h l n. BITS h l n = (n MOD 2 EXP SUC h) DIV 2 EXP l`,
  RW_TAC std_ss [BITS_THM,DIV_MOD_MOD_DIV2]
);

val BITS_COMP_LEM = prove(
  `!h1 l1 h2 l2 n. 
      h2 + l1 <= h1 ==> 
       (((n DIV 2 EXP l1) MOD 2 EXP (h1 - l1) DIV 2 EXP l2) MOD 2 EXP (h2-l2)
         =
       (n DIV 2 EXP (l2 + l1)) MOD 2 EXP ((h2 + l1) - (l2 + l1)))`,
  REPEAT STRIP_TAC
    THEN REWRITE_TAC [SPECL 
          [`(n DIV 2 EXP l1) MOD 2 EXP (h1 - l1)`,`l2`,`h2`] DIV_MOD_MOD_DIV2]
    THEN IMP_RES_TAC LESS_EQUAL_ADD
    THEN POP_ASSUM (fn th => 
           SIMP_TAC arith_ss [EXP_ADD,MOD_MULT_MOD,ZERO_LT_TWOEXP,th])
    THEN REWRITE_TAC [SPECL [`n`,`l1`,`p`] DIV_MOD_MOD_DIV]
    THEN SIMP_TAC arith_ss [DIV_DIV_DIV_MULT,ZERO_LT_TWOEXP,GSYM EXP_ADD]
    THEN REWRITE_TAC [SIMP_RULE arith_ss [] 
                       (SPECL [`n`,`l1 + l2`,`h2 + l1`] DIV_MOD_MOD_DIV2)]
);

val BITS_COMP_THM = store_thm("BITS_COMP_THM",
  `!h1 l1 h2 l2 n. h2 + l1 <= h1 
                    ==> (BITS h2 l2 (BITS h1 l1 n) = BITS (h2+l1) (l2+l1) n)`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_EQ_MONO
    THEN FULL_SIMP_TAC std_ss [BITS_THM,GSYM ADD_CLAUSES,BITS_COMP_LEM]
);

val BITS_DIV_THM = store_thm("BITS_DIV_THM",
  `!h l x n. (BITS h l x) DIV 2 EXP n = BITS h (l + n) x`,
  RW_TAC std_ss [BITS2_THM,EXP_ADD,ZERO_LT_TWOEXP,DIV_DIV_DIV_MULT]
);

val BITS_LT_HIGH = store_thm("BITS_LT_HIGH",
  `!h l n. n < 2 EXP SUC h ==> (BITS h l n = n DIV 2 EXP l)`,
  RW_TAC std_ss [BITS2_THM,LESS_MOD]
);

(* -------------------------------------------------------- *)

val MOD2_EQ_0 = prove(
  `!q. (q * 2) MOD 2 = 0`,
  RW_TAC arith_ss [MOD_EQ_0]
);
 
val ONE_TWO_LEM = prove(
  `!n. (n MOD 2 = 0) \/ (n MOD 2 = 1)`,
  `!n. n < 2 ==> ((n = 0) \/ (n = 1))` by DECIDE_TAC
    THEN RW_TAC arith_ss [DIVISION]
);
 
val NOT_MOD2_LEM = store_thm("NOT_MOD2_LEM",
  `!n. ~(n MOD 2 = 0) = (n MOD 2 = 1)`,
  STRIP_TAC THEN EQ_TAC
    THENL [PROVE_TAC [ONE_TWO_LEM],DECIDE_TAC]
);

val EVEN_MOD2_LEM = store_thm("EVEN_MOD2_LEM",
  `!n. EVEN n = ((n MOD 2) = 0)`,
  RW_TAC std_ss [ONCE_REWRITE_RULE [MULT_COMM] EVEN_EXISTS]
    THEN EQ_TAC THEN STRIP_TAC
    THENL [
      ASM_REWRITE_TAC [MOD2_EQ_0],
      EXISTS_TAC `n DIV 2`
        THEN `0 < 2n` by DECIDE_TAC
        THEN IMP_RES_TAC DIVISION
        THEN POP_ASSUM (K ALL_TAC)
        THEN POP_ASSUM (fn th => ASSUME_TAC (SPEC `n` th))
        THEN RW_TAC arith_ss []
    ]
);
 
val ODD_MOD2_LEM = store_thm("ODD_MOD2_LEM",
 `!n. ODD n = ((n MOD 2) = 1)`,
 STRIP_TAC THEN REWRITE_TAC [ODD_EVEN,EVEN_MOD2_LEM,NOT_MOD2_LEM]
);

(* -------------------------------------------------------- *)

(* -------------------------------------------------------- *)

val DIV1 = save_thm("DIV1",REDUCE_RULE DIV_ONE);

val LSB_ODD = store_thm("LSB_ODD",
  `LSB = ODD`,
  ONCE_REWRITE_TAC [FUN_EQ_THM]
    THEN SIMP_TAC arith_ss [ODD_MOD2_LEM,LSB_def,BIT_def,BITS2_THM,EXP,DIV1]
);

(* -------------------------------------------------------- *)

val LESS_MULT_MONO_SPEC = GEN_ALL (REWRITE_RULE [SYM TWO] 
                                   (SPECL [`m`,`i`,`1`] LESS_MULT_MONO));
 
val LESS_MULT_MONO_SPEC2 = prove(
  `!a b. a < b ==> 2 * a + 1 < 2 * b`,
  RW_TAC arith_ss []
);

val ADD_DIV_ADD_DIV2 = save_thm("ADD_DIV_ADD_DIV2",
  ONCE_REWRITE_RULE [MULT_COMM] 
    (SIMP_RULE arith_ss [] (SPEC `2` ADD_DIV_ADD_DIV))
);

val ADD_DIV_ADD_DIV3 = save_thm("ADD_DIV_ADD_DIV3",
  ONCE_REWRITE_RULE [ADD_COMM] ADD_DIV_ADD_DIV2
);

val BIT_DIV2 = store_thm("BIT_DIV2",
  `!i. BIT n (i DIV 2) = BIT (SUC n) i`,
  RW_TAC arith_ss [BIT_def,BITS_THM,EXP,ZERO_LT_TWOEXP,DIV_DIV_DIV_MULT]
);

val BITWISE_LT_2EXP = store_thm("BITWISE_LT_2EXP",
  `!n op a b. BITWISE n op a b < 2 EXP n`,
  Induct_on `n`
    THEN REPEAT STRIP_TAC
    THENL [
      SIMP_TAC arith_ss [BITWISE_def],
      FULL_SIMP_TAC arith_ss [BITWISE_def,EXP]
        THEN RW_TAC arith_ss [LESS_MULT_MONO_SPEC,LESS_MULT_MONO_SPEC2]
    ]
);

val BITWISE_THM = store_thm("BITWISE_THM",
  `!x n op a b. x < n ==> (BIT x (BITWISE n op a b) = op (BIT x a) (BIT x b))`,
  Induct_on `n`
    THENL [
      RW_TAC arith_ss [],
      Induct_on `x`
        THENL [
           RW_TAC arith_ss [BITWISE_def,LSB_def]
             THEN SIMP_TAC arith_ss [BIT_def,BITS2_THM,EXP,
                                      ONCE_REWRITE_RULE [MULT_COMM] MOD_MULT,
                                      ONCE_REWRITE_RULE [MULT_COMM] MOD_EQ_0],
           RW_TAC arith_ss [BITWISE_def,LSB_def]
             THEN `BIT x (BITWISE n op (a DIV 2) (b DIV 2)) =
                    op (BIT x (a DIV 2)) (BIT x (b DIV 2))` by PROVE_TAC []
             THEN RULE_ASSUM_TAC (REWRITE_RULE [BIT_DIV2])
             THEN POP_ASSUM (fn th => REWRITE_TAC [SYM th])
             THEN SIMP_TAC arith_ss [GSYM BIT_DIV2,ADD_DIV_ADD_DIV3,
                                      ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
         ]
    ]
);

val BITWISE_COR = store_thm("BITWISE_COR",
  `!x n op a b. 
      x < n ==> 
      op (BIT x a) (BIT x b) ==> 
     ((BITWISE n op a b DIV 2 EXP x) MOD 2 = 1)`,
  NTAC 6 STRIP_TAC
    THEN IMP_RES_TAC BITWISE_THM
    THEN NTAC 2 (WEAKEN_TAC (K true))
    THEN POP_ASSUM (fn th => REWRITE_TAC [GSYM th])
    THEN ASM_SIMP_TAC std_ss 
    [BITS_THM,BIT_def,DIV1,EXP_1,DECIDE(Term`SUC x - x = 1`)]
);
 
val BITWISE_NOT_COR = store_thm("BITWISE_NOT_COR",
  `!x n op a b. 
     x < n ==> 
     ~op (BIT x a) (BIT x b) ==> 
    ((BITWISE n op a b DIV 2 EXP x) MOD 2 = 0)`,
  NTAC 6 STRIP_TAC
    THEN IMP_RES_TAC BITWISE_THM
    THEN NTAC 2 (WEAKEN_TAC (K true))
    THEN POP_ASSUM (fn th => REWRITE_TAC [GSYM th])
    THEN ASM_SIMP_TAC std_ss [BITS_THM,BIT_def,GSYM NOT_MOD2_LEM,DIV1,EXP_1,
                              DECIDE(Term`SUC x - x = 1`)]
);

val DIV_MULT_THM = store_thm("DIV_MULT_THM",
  `!x n. n DIV 2 EXP x * 2 EXP x = n - n MOD 2 EXP x`,
  RW_TAC arith_ss [DIV_MULT_LESS_EQ,MOD_2EXP_LEM,SUB_SUB]
);
 
val DIV_MULT_THM2 = save_thm("DIV_MULT_THM2",
  ONCE_REWRITE_RULE [MULT_COMM] (REWRITE_RULE [EXP_1] (SPEC `1` DIV_MULT_THM))
);

val MULT_INCREASES2 = 
 ONCE_REWRITE_RULE [MULT_COMM] (REWRITE_RULE [GSYM LESS_EQ] MULT_INCREASES);

val ONE_LT_TWOEXP_SUCN = prove(
  `!n. 1 < 2 EXP n * 2`,
  Induct_on `n` THEN RW_TAC arith_ss [EXP,MULT_INCREASES2]
);
 
val TWOEXP_MONO = store_thm("TWOEXP_MONO",
  `!a b. a < b ==> 2 EXP a < 2 EXP b`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_ADD_1
    THEN ASM_SIMP_TAC arith_ss 
           [EXP_ADD,MULT_INCREASES2,ONE_LT_TWOEXP_SUCN,ZERO_LT_TWOEXP]
);
 
val TWOEXP_MONO2 = store_thm("TWOEXP_MONO2",
  `!a b. a <= b ==> 2 EXP a <= 2 EXP b`,
  REPEAT STRIP_TAC
    THEN Cases_on `b = a`
    THEN FULL_SIMP_TAC arith_ss [GSYM NOT_LESS]
    THEN IMP_RES_TAC LESS_CASES_IMP
    THEN RW_TAC std_ss [TWOEXP_MONO,NOT_LESS,LESS_IMP_LESS_OR_EQ]
);

(* -------------------------------------------------------- *)

val SLICE_LEM1 = store_thm("SLICE_LEM1",
  `!a x y. a DIV 2 EXP (x+y) * 2 EXP (x+y) =
       a DIV 2 EXP x * 2 EXP x - (a DIV 2 EXP x) MOD 2 EXP y * 2 EXP x`,
  REPEAT STRIP_TAC
    THEN SIMP_TAC std_ss [EXP_ADD]
    THEN SUBST_OCCS_TAC [([2],SPECL [`2 EXP x`,`2 EXP y`] MULT_COMM)]
    THEN SIMP_TAC std_ss [ZERO_LT_TWOEXP,GSYM DIV_DIV_DIV_MULT,MULT_ASSOC,
             SPECL [`y`,`a DIV 2 EXP x`] DIV_MULT_THM,RIGHT_SUB_DISTRIB]
);

val SLICE_LEM2 = store_thm("SLICE_LEM2",
  `!a x y. n MOD 2 EXP (x+y) 
            = 
           n MOD 2 EXP x + (n DIV 2 EXP x) MOD 2 EXP y * 2 EXP x`,
  REPEAT STRIP_TAC
    THEN SIMP_TAC std_ss [DIV_MULT_LESS_EQ,MOD_2EXP_LEM,SLICE_LEM1,
                          RIGHT_SUB_DISTRIB,SUB_SUB,SUB_LESS_EQ]
    THEN Cases_on `n = n DIV 2 EXP x * 2 EXP x`
    THENL [
       POP_ASSUM (fn th => SIMP_TAC arith_ss [SYM th]),
       ASSUME_TAC (REWRITE_RULE [GSYM NOT_LESS] DIV_MULT_LESS_EQ)
         THEN IMP_RES_TAC LESS_CASES_IMP
         THEN RW_TAC std_ss [SUB_RIGHT_ADD]
         THEN PROVE_TAC [GSYM NOT_LESS_EQUAL]
    ]
);

val SLICE_LEM3 = store_thm("SLICE_LEM3",
  `!n h l. l < h ==> n MOD 2 EXP SUC l <= n MOD 2 EXP h`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_ADD_1
    THEN POP_ASSUM (fn th => REWRITE_TAC [th])
    THEN REWRITE_TAC [GSYM ADD1,GSYM ADD_SUC,GSYM (CONJUNCT2 ADD)]
    THEN RW_TAC arith_ss [SLICE_LEM2]
);

val SLICE_THM = store_thm("SLICE_THM",
  `!n h l. SLICE h l n = BITS h l n * 2 EXP l`,
  REPEAT STRIP_TAC
    THEN REWRITE_TAC [SLICE_def,BITS_def,MOD_2EXP_def,DIV_2EXP_def]
    THEN Cases_on `h < l`
    THENL [
      IMP_RES_TAC SLICE_LEM3
        THEN POP_ASSUM (fn th => ASSUME_TAC (SPEC `n` th))
        THEN IMP_RES_TAC LESS_OR
        THEN IMP_RES_TAC SUB_EQ_0
        THEN ASM_SIMP_TAC arith_ss [EXP,REDUCE_RULE MOD_ONE,MULT_CLAUSES],
      REWRITE_TAC [DIV_MOD_MOD_DIV2]
        THEN RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS])
        THEN SUBST_OCCS_TAC [([1],CONJUNCT1 (SPEC `n MOD 2 EXP SUC h` (
                SIMP_RULE std_ss [ZERO_LT_TWOEXP] (SPEC `2 EXP l` DIVISION))))]
        THEN IMP_RES_TAC LESS_EQUAL_ADD
        THEN POP_ASSUM (fn th => SUBST_OCCS_TAC [([2],th)])
        THEN SIMP_TAC std_ss 
               [ADD_SUC,ADD_SUB,MOD_MULT_MOD,ZERO_LT_TWOEXP,EXP_ADD]
    ]
);

val SLICELT_THM = store_thm("SLICELT_THM",
  `!h l n. SLICE h l n < 2 EXP SUC h`,
  REPEAT STRIP_TAC
    THEN ASSUME_TAC 
           (CONJUNCT2 
              (SPEC `n` 
                (SIMP_RULE std_ss [ZERO_LT_TWOEXP] 
                   (SPEC `2 EXP SUC h` DIVISION))))
    THEN RW_TAC arith_ss 
          [SLICE_def,MOD_2EXP_def,ZERO_LT_TWOEXP,SUB_RIGHT_LESS]);
 
val BITS_SLICE_THM = store_thm("BITS_SLICE_THM",
  `!h l n. BITS h l (SLICE h l n) = BITS h l n`,
  RW_TAC std_ss [SLICELT_THM,BITS_LT_HIGH,ZERO_LT_TWOEXP,SLICE_THM,MULT_DIV]
);

val MOD_2EXP_MONO = store_thm("MOD_2EXP_MONO",
  `!n h l. l <= h ==> n MOD 2 EXP l <= n MOD 2 EXP SUC h`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_EQ_EXISTS
    THEN POP_ASSUM (fn th => REWRITE_TAC [th])
    THEN `SUC (l + p) = l + SUC p` by DECIDE_TAC
    THEN RW_TAC arith_ss [SLICE_LEM2]
);

val SLICE_COMP_THM = store_thm("SLICE_COMP_THM",
  `!h m l n. (SUC m) <= h /\ l <= m 
              ==> 
             (SLICE h (SUC m) n + SLICE m l n = SLICE h l n)`,
  RW_TAC std_ss 
     [SLICE_def,MOD_2EXP_def,MOD_2EXP_MONO,GSYM LESS_EQ_ADD_SUB,SUB_ADD]
);

(* -------------------------------------------------------- *)

val _ = export_theory();
 
(* -------------------------------------------------------- *)
