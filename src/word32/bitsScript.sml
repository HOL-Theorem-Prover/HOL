(* app load ["bossLib"]; *)
open HolKernel boolLib Parse Q bossLib simpLib numLib
     pairTheory numeralTheory arithmeticTheory prim_recTheory;

infix 8 by;
infix THEN THENC THENL ++;
 

(* -------------------------------------------------------- *)

val _ = new_theory "bits";

(* -------------------------------------------------------- *)

val TIMES_2EXP_def  = Define `TIMES_2EXP x n = n * 2 EXP x`;

val DIV_2EXP_def    = Define `DIV_2EXP x n = n DIV 2 EXP x`;

val MOD_2EXP_def    = Define `MOD_2EXP x n = n MOD 2 EXP x`;

val DIVMOD_2EXP_def = Define `DIVMOD_2EXP x n = (n DIV 2 EXP x,n MOD 2 EXP x)`;
 
val SET_def         = Define `SET b n = if b then 2 EXP n else 0`;
 
val BITS_def        = Define `BITS h l n = MOD_2EXP (SUC h-l) (DIV_2EXP l n)`;
 
val BIT_def         = Define `BIT b n = (BITS b b n = 1)`;
 
val SLICE_def       = Define `SLICE h l n = MOD_2EXP (SUC h) n - MOD_2EXP l n`;
 
val LSB_def         = Define `LSB = BIT 0`;

val BITWISE_def =
 Define
   `(BITWISE 0 op x y = 0)
 /\ (BITWISE (SUC n) op x y =
         BITWISE n op x y + SET (op (BIT n x) (BIT n y)) n)`;

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

val DIV1 = save_thm("DIV1",REDUCE_RULE DIV_ONE);

val LSB_ODD = store_thm("LSB_ODD",
  `LSB = ODD`,
  ONCE_REWRITE_TAC [FUN_EQ_THM]
    THEN SIMP_TAC arith_ss [ODD_MOD2_LEM,LSB_def,BIT_def,BITS2_THM,EXP,DIV1]
);

(* -------------------------------------------------------- *)

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

val LESS_EXP_MULT = store_thm("LESS_EXP_MULT",
  `!a b. a < b ==> ?p. 2 EXP b = p * 2 EXP a`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_ADD
    THEN RULE_ASSUM_TAC (ONCE_REWRITE_RULE [SIMP_RULE arith_ss [] (SPEC `2` (GSYM EXP_INJECTIVE))])
    THEN EXISTS_TAC `2 EXP p`
    THEN FULL_SIMP_TAC arith_ss [EXP_ADD]
);
 
val LESS_EQ_EXP_MULT = store_thm("LESS_EQ_EXP_MULT",
  `!a b. a <= b ==> ?p. 2 EXP b = p * 2 EXP a`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_EQUAL_ADD
    THEN RULE_ASSUM_TAC (ONCE_REWRITE_RULE [SIMP_RULE arith_ss [] (SPEC `2` (GSYM EXP_INJECTIVE))])
    THEN EXISTS_TAC `2 EXP p`
    THEN FULL_SIMP_TAC arith_ss [EXP_ADD,MULT_COMM]
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

val SUC_SUB = SIMP_CONV arith_ss [ADD1] ``SUC a - a``;
 
val NOT_BIT = store_thm("NOT_BIT",
  `!n a. ~BIT n a = (BITS n n a = 0)`,
  RW_TAC std_ss [BIT_def,BITS_THM,SUC_SUB,EXP_1,GSYM NOT_MOD2_LEM]
);
 
val NOT_BITS = store_thm("NOT_BITS",
  `!n a. ~(BITS n n a = 0) = (BITS n n a = 1)`,
  RW_TAC std_ss [GSYM NOT_BIT,GSYM BIT_def]
);
 
val BIT_SLICE = store_thm("BIT_SLICE",
  `!n a b. (BIT n a = BIT n b) = (SLICE n n a = SLICE n n b)`,
  REPEAT STRIP_TAC THEN EQ_TAC
    THENL [
      Cases_on `BIT n a`
        THEN FULL_SIMP_TAC arith_ss [BIT_def,SLICE_THM]
        THEN FULL_SIMP_TAC arith_ss [GSYM NOT_BITS],
      Cases_on `BITS n n a = 1`
        THEN Cases_on `BITS n n b = 1`
        THEN FULL_SIMP_TAC arith_ss [BIT_def,SLICE_THM]
        THEN FULL_SIMP_TAC arith_ss [GSYM NOT_BITS,MULT_CLAUSES,
                                     REWRITE_RULE [GSYM NOT_ZERO_LT_ZERO] ZERO_LT_TWOEXP]
    ]
);

val BITS_ZERO = store_thm("BITS_ZERO",
  `!h l n. h < l ==> (BITS h l n = 0)`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_ADD_1
    THEN POP_ASSUM (fn th => REWRITE_TAC [th])
    THEN ASSUME_TAC (REWRITE_RULE [EXP,SUB,SUB_EQUAL_0]
                       (ONCE_REWRITE_RULE [SUB_PLUS]
                          (REWRITE_RULE [ADD1] (SPECL [`h`,`h + 1 + p`,`n`] BITSLT_THM))))
    THEN FULL_SIMP_TAC arith_ss []
);
 
val SUB_BITS = prove(
  `!h l a b. (BITS (SUC h) l a = BITS (SUC h) l b) ==> (BITS h l a = BITS h l b)`,
  REPEAT STRIP_TAC
    THEN Cases_on `h < l`
    THENL [
      RW_TAC std_ss [BITS_ZERO],
      RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS])
        THEN POP_ASSUM (fn th =>
               ONCE_REWRITE_TAC [GSYM (SIMP_RULE arith_ss [th,SUB_ADD]
               (SPECL [`SUC h`,`l`,`h-l`,`0`] BITS_COMP_THM))])
        THEN ASM_REWRITE_TAC []
    ]
);

val DECEND_LEMMA = prove(
  `!P l y.  (!x. l <= x /\ x <= SUC y ==> P x) ==> (!x. l <= x /\ x <= y ==> P x)`,
  RW_TAC arith_ss []
);
 
(* |- !m n. m < SUC n ==> m <= n *)
val LESS_LEMMA3 = REWRITE_RULE [ONCE_REWRITE_RULE [DISJ_COMM] (GSYM LESS_OR_EQ)] LESS_LEMMA1;

val BITS_SUC = prove(
  `!h l a. BITS (SUC h) l a = if l = SUC h then
                                BITS (SUC h) l (SLICE (SUC h) (SUC h) a)
                              else
                                BITS (SUC h) l (SLICE (SUC h) (SUC h) a + BITS h l a * 2 EXP l)`,
  REPEAT STRIP_TAC
    THEN Cases_on `SUC h < l`
    THENL [
      RW_TAC std_ss [BITS_ZERO],
      RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS])
        THEN RW_TAC arith_ss [GSYM SLICE_THM,BITS_SLICE_THM]
        THEN `l < SUC h` by ASM_SIMP_TAC arith_ss []
        THEN IMP_RES_TAC LESS_LEMMA3
        THEN ASM_SIMP_TAC std_ss [BITS_SLICE_THM,SIMP_RULE arith_ss [] (SPECL [`SUC h`,`h`] SLICE_COMP_THM)]
      ]
);

val BIT_BITS_LEM = prove(
  `!h l a b. l <= h ==> (BITS h l a = BITS h l b) ==> (BIT h a = BIT h b)`,
  RW_TAC std_ss [BIT_SLICE,SLICE_THM]
    THEN PAT_ASSUM `l <= h` (fn th =>
               ONCE_REWRITE_TAC [GSYM (SIMP_RULE arith_ss [th,SUB_ADD]
               (SPECL [`h`,`l`,`h-l`,`h-l`] BITS_COMP_THM))])
    THEN ASM_REWRITE_TAC []
);

val BIT_BITS_THM = store_thm("BIT_BITS_THM",
  `!h l a b. (!x. l <= x /\ x <= h ==> (BIT x a = BIT x b)) = (BITS h l a = BITS h l b)`,
  Induct_on `h`
    THEN REPEAT STRIP_TAC
    THENL [
      Cases_on `l = 0`
        THEN RW_TAC arith_ss [BIT_SLICE,SLICE_THM,EXP,SPEC `0` BITS_ZERO,NOT_ZERO_LT_ZERO],
      EQ_TAC THEN REPEAT STRIP_TAC
        THENL [
          ONCE_REWRITE_TAC [BITS_SUC]
            THEN RW_TAC std_ss []
            THENL [
               POP_ASSUM (fn th => SIMP_TAC std_ss [SIMP_RULE arith_ss [BIT_SLICE] (SPEC `SUC h` th)]),
               Cases_on `SUC h < l`
                 THENL [
                   RW_TAC std_ss [BITS_ZERO],
                   RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS])
                     THEN PAT_ASSUM `!x. l <= x /\ x <= SUC h ==> (BIT x a = BIT x b)`
                            (fn th => ASM_SIMP_TAC std_ss [SIMP_RULE arith_ss [BIT_SLICE] (SPEC `SUC h` th)]
                            THEN ASSUME_TAC th)
                     THEN POP_ASSUM (fn th => ASSUME_TAC (MATCH_MP
                           (BETA_RULE (SPECL [`\x. BIT x a = BIT x b`,`l`,`h`] DECEND_LEMMA)) th))
                     THEN PAT_ASSUM `!l a b.  (!x. l <= x /\ x <= h ==> (BIT x a = BIT x b)) =
                                              (BITS h l a = BITS h l b)`
                            (fn th => ASSUME_TAC (SPECL [`l`,`a`,`b`] th))
                     THEN FULL_SIMP_TAC std_ss []
                 ]
            ],
          IMP_RES_TAC SUB_BITS
            THEN PAT_ASSUM `!l a b. (!x. l <= x /\ x <= h ==> (BIT x a = BIT x b)) =
                                    (BITS h l a = BITS h l b)`
                   (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM (SPECL [`l`,`a`,`b`] th)]))
            THEN Cases_on `x <= h`
            THEN ASM_SIMP_TAC std_ss []
            THEN `x = SUC h` by ASM_SIMP_TAC arith_ss []
            THEN Cases_on `l = SUC h`
            THENL [
              FULL_SIMP_TAC std_ss [BIT_def],
              `l <= SUC h` by ASM_SIMP_TAC arith_ss []
                THEN POP_ASSUM (fn th => ASSUME_TAC (SIMP_RULE std_ss [th] (SPECL [`SUC h`,`l`,`a`,`b`] BIT_BITS_LEM)))
                THEN FULL_SIMP_TAC std_ss []
            ]
        ]
    ]
);

(* -------------------------------------------------------- *)

val BITWISE_LT_2EXP = store_thm("BITWISE_LT_2EXP",
  `!n op a b. BITWISE n op a b < 2 EXP n`,
  Induct_on `n`
    THEN RW_TAC std_ss [ADD_0,TIMES2,LESS_IMP_LESS_ADD,LESS_MONO_ADD,BITWISE_def,SET_def,EXP]
    THEN REDUCE_TAC
);

val LESS_EXP_MULT2 = store_thm("LESS_EXP_MULT2",
  `!a b. a < b ==> ?p. 2 EXP b = 2 EXP (p+1) * 2 EXP a`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_ADD_1
    THEN RULE_ASSUM_TAC (ONCE_REWRITE_RULE [SIMP_RULE arith_ss [] (SPEC `2` (GSYM EXP_INJECTIVE))])
    THEN EXISTS_TAC `p`
    THEN FULL_SIMP_TAC arith_ss [EXP_ADD,MULT_COMM]
);

val BITWISE_LEM = store_thm("BITWISE_THM",
  `!n op a b. BIT n (BITWISE (SUC n) op a b) = op (BIT n a) (BIT n b)`,
  RW_TAC arith_ss [SET_def,BITWISE_def,NOT_BIT]
    THENL [
       SIMP_TAC arith_ss [BIT_def,BITS_THM,SUC_SUB,SIMP_RULE arith_ss []
                (SPEC `1` (SIMP_RULE std_ss [BITWISE_LT_2EXP]
                   (SPECL [`2 EXP n`,`BITWISE n op a b`] DIV_MULT)))],
       SIMP_TAC arith_ss [BITS_THM,LESS_DIV_EQ_ZERO,BITWISE_LT_2EXP,SUC_SUB]
    ]
);

(* !x. 2 EXP (SUC x - x) = 2 *)
val TWO_SUC_SUB = GEN_ALL (SIMP_CONV std_ss [SUC_SUB,EXP_1] ``2 EXP (SUC x - x)``);

val LEFT_REWRITE_TAC = GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) empty_rewrites;

val BITWISE_THM = store_thm("BITWISE_THM",
  `!x n op a b. x < n ==> (BIT x (BITWISE n op a b) = op (BIT x a) (BIT x b))`,
  Induct_on `n`
    THEN REPEAT STRIP_TAC
    THENL [
      FULL_SIMP_TAC arith_ss [],
      Cases_on `x = n`
        THENL [
           ASM_SIMP_TAC std_ss [BITWISE_LEM],
           `x < n` by ASM_SIMP_TAC arith_ss []
              THEN RW_TAC arith_ss [BITWISE_def,SET_def]
              THEN LEFT_REWRITE_TAC [BIT_def]
              THEN ASM_SIMP_TAC std_ss [BITS_THM]
              THEN IMP_RES_TAC LESS_EXP_MULT2
              THEN POP_ASSUM (K ALL_TAC)
              THEN ASM_SIMP_TAC std_ss [ZERO_LT_TWOEXP,ADD_DIV_ADD_DIV,TWO_SUC_SUB,GSYM ADD1,EXP,
                      ONCE_REWRITE_RULE [MULT_COMM] (REWRITE_RULE [DECIDE(Term`0 < 2`)] (SPEC `2` MOD_TIMES))]
              THEN SUBST_OCCS_TAC [([2],SYM (SPEC `x` TWO_SUC_SUB))]
              THEN ASM_SIMP_TAC std_ss [GSYM BITS_THM,GSYM BIT_def]
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
    [BITS_THM,BIT_def,DIV1,EXP_1,SUC_SUB]
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
    THEN ASM_SIMP_TAC std_ss [BITS_THM,BIT_def,GSYM NOT_MOD2_LEM,DIV1,EXP_1,SUC_SUB]
);

(* -------------------------------------------------------- *)

val _ = export_theory();
 
(* -------------------------------------------------------- *)
