(* load "wordUtil"; *)
open HolKernel Parse boolLib bossLib Q simpLib numLib
     arithmeticTheory prim_recTheory wordUtil;

val arith_ss = old_arith_ss
(* -------------------------------------------------------- *)

val _ = new_theory "bits";

(* -------------------------------------------------------- *)

fun Def s = curry Definition.new_definition s o Parse.Term;

val TIMES_2EXP_def  = Def "TIMES_2EXP_def"
                          `TIMES_2EXP x n = n * 2 EXP x`;

val DIV_2EXP_def    = Def "DIV_2EXP_def"
                          `DIV_2EXP x n = n DIV 2 EXP x`;

val DIVMOD_2EXP_def = Def "DIVMOD_2EXP_def"
                         `DIVMOD_2EXP x n = (n DIV 2 EXP x,n MOD 2 EXP x)`;

val SBIT_def        = Def "SBIT_def"
                          `SBIT b n = if b then 2 EXP n else 0`;

val BITS_def        = Def "BITS_def"
                          `BITS h l n = MOD_2EXP (SUC h-l) (DIV_2EXP l n)`;

val BITV_def        = Def "BITV_def"
                          `BITV n b = BITS b b n`;

val BIT_def         = Def "BIT_def"
                          `BIT b n = (BITS b b n = 1)`;

val SLICE_def       = Def "SLICE_def"
                          `SLICE h l n = MOD_2EXP (SUC h) n - MOD_2EXP l n`;

val LSBn_def        = Def "LSBn_def"
                          `LSBn = BIT 0`;

val BITWISE_def =
 Prim_rec.new_recursive_definition
  {name = "BITWISE_def",
   def = ``(BITWISE 0 op x y = 0)
        /\ (BITWISE (SUC n) op x y =
              BITWISE n op x y + SBIT (op (BIT n x) (BIT n y)) n)``,
   rec_axiom = prim_recTheory.num_Axiom}

val SIGN_EXTEND_def =
  Def "SIGN_EXTEND_def"
      `SIGN_EXTEND l h n =
         let m = n MOD 2 EXP l in
         if BIT (l - 1) n then 2 EXP h - 2 EXP l + m else m`;

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val DIVMOD_2EXP = save_thm("DIVMOD_2EXP",
  REWRITE_RULE [GSYM DIV_2EXP_def,GSYM MOD_2EXP_def] DIVMOD_2EXP_def
);

(* -------------------------------------------------------- *)

val SUC_SUB = save_thm("SUC_SUB",SIMP_CONV arith_ss [ADD1] ``SUC a - a``);

(* |- !n r. r < n ==> ((n + r) DIV n = 1) *)
val DIV_MULT_1 = save_thm("DIV_MULT_1",
  (GEN_ALL o SIMP_RULE arith_ss [] o INST [`q` |-> `1`] o SPEC_ALL
           o CONV_RULE (ONCE_DEPTH_CONV RIGHT_IMP_FORALL_CONV)) DIV_MULT
);

(* |- !m. ~(m = 0) ==> ?p. m = SUC p *)
val NOT_ZERO_ADD1 = save_thm("NOT_ZERO_ADD1",
  (GEN_ALL o REWRITE_RULE [GSYM NOT_ZERO_LT_ZERO,GSYM ADD1,ADD] o SPECL [`m`,`0`]) LESS_ADD_1
);

val ZERO_LT_TWOEXP = save_thm("ZERO_LT_TWOEXP",
  GEN_ALL (REDUCE_RULE (SPECL [`n`,`1`] ZERO_LESS_EXP))
);

val TWOEXP_NOT_ZERO = save_thm("TWOEXP_NOT_ZERO",
  REWRITE_RULE [GSYM NOT_ZERO_LT_ZERO] ZERO_LT_TWOEXP
);

val th = (SPEC_ALL o REWRITE_RULE [ZERO_LT_TWOEXP] o SPEC `2 EXP n`) DIVISION;

(* |- !n k. k MOD 2 EXP n < 2 EXP n *)
val MOD_2EXP_LT = save_thm("MOD_2EXP_LT",
  (GEN_ALL o CONJUNCT2) th
);

(* |- !n k. k = k DIV 2 EXP n * 2 EXP n + k MOD 2 EXP n *)
val TWOEXP_DIVISION = save_thm("TWOEXP_DIVISION",
  (GEN_ALL o CONJUNCT1) th
);

val MULT_INCREASES2 = ONCE_REWRITE_RULE [MULT_COMM] (REWRITE_RULE [GSYM LESS_EQ] MULT_INCREASES);

val ONE_LT_TWOEXP_SUCN = prove(
  `!n. 1 < 2 EXP n * 2`,
  Induct_on `n` THEN A_RW_TAC [EXP,MULT_INCREASES2]
);

val TWOEXP_MONO = store_thm("TWOEXP_MONO",
  `!a b. a < b ==> 2 EXP a < 2 EXP b`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_ADD_1
    THEN ASM_A_SIMP_TAC [EXP_ADD,MULT_INCREASES2,ONE_LT_TWOEXP_SUCN,ZERO_LT_TWOEXP]
);

val TWOEXP_MONO2 = store_thm("TWOEXP_MONO2",
  `!a b. a <= b ==> 2 EXP a <= 2 EXP b`,
  REPEAT STRIP_TAC
    THEN Cases_on `b = a`
    THEN A_FULL_SIMP_TAC [GSYM NOT_LESS]
    THEN IMP_RES_TAC LESS_CASES_IMP
    THEN B_RW_TAC [TWOEXP_MONO,NOT_LESS,LESS_IMP_LESS_OR_EQ]
);

val EXP_SUB_LESS_EQ = store_thm("EXP_SUB_LESS_EQ",
  `!a b. 2 EXP (a - b) <= 2 EXP a`,
  B_RW_TAC [SUB_LESS_EQ,TWOEXP_MONO2]
);

(* -------------------------------------------------------- *)

val BITS_THM = save_thm("BITS_THM",
  REWRITE_RULE [DIV_2EXP_def,MOD_2EXP_def] BITS_def
);

val BITSLT_THM = store_thm("BITSLT_THM",
  `!h l n. BITS h l n < 2 EXP (SUC h-l)`,
  B_RW_TAC [BITS_THM,ZERO_LT_TWOEXP,DIVISION]
);

val DIV_MULT_LEM = prove(
  `!m n. 0 < n ==> m DIV n * n <= m`,
  A_RW_TAC [LESS_EQ_EXISTS]
    THEN EXISTS_TAC `m MOD n`
    THEN A_RW_TAC [GSYM DIVISION]
);

(* |- !x n. n DIV 2 EXP x * 2 EXP x <= n *)
val DIV_MULT_LESS_EQ = GEN_ALL (SIMP_RULE bool_ss [ZERO_LT_TWOEXP] (SPECL [`n`,`2 EXP x`] DIV_MULT_LEM));

val MOD_2EXP_LEM = prove(
  `!n x. n MOD 2 EXP x = n - n DIV 2 EXP x * 2 EXP x`,
  A_RW_TAC [DIV_MULT_LESS_EQ,GSYM ADD_EQ_SUB,ZERO_LT_TWOEXP,GSYM DIVISION]
);

val DIV_MULT_LEM2 = prove(
  `!a b p. a DIV 2 EXP (b + p) * 2 EXP (p + b) <= a DIV 2 EXP b * 2 EXP b`,
  B_RW_TAC [SPECL [`a DIV 2 EXP b`,`2 EXP p`] DIV_MULT_LEM,
            EXP_ADD,MULT_ASSOC,GSYM DIV_DIV_DIV_MULT,ZERO_LT_TWOEXP,LESS_MONO_MULT]
);

val MOD_EXP_ADD = prove(
  `!a b p. a MOD 2 EXP (b + p) = a MOD 2 EXP b + (a DIV 2 EXP b) MOD 2 EXP p * 2 EXP b`,
  REPEAT STRIP_TAC
    THEN B_SIMP_TAC [MOD_2EXP_LEM,RIGHT_SUB_DISTRIB,DIV_DIV_DIV_MULT,
                     ZERO_LT_TWOEXP,GSYM MULT_ASSOC,GSYM EXP_ADD]
    THEN ASSUME_TAC (
           (GSYM o SPECL [`a DIV 2 EXP (b + p) * 2 EXP (p + b)`,`a DIV 2 EXP b * 2 EXP b`]) LESS_EQ_ADD_SUB)
    THEN ASM_A_SIMP_TAC [DIV_MULT_LEM2,DIV_MULT_LEM,ZERO_LT_TWOEXP,SUB_ADD]
);

val DIV_MOD_MOD_DIV = prove(
  `!a b p. (a DIV 2 EXP b) MOD 2 EXP p = a MOD 2 EXP (b + p) DIV 2 EXP b`,
  A_RW_TAC [MOD_EXP_ADD,ADD_DIV_ADD_DIV,ZERO_LT_TWOEXP,LESS_DIV_EQ_ZERO,DIVISION]
);

val DIV_MOD_MOD_DIV2 = prove(
  `!a b c. (a DIV 2 EXP b) MOD 2 EXP (c - b) = (a MOD 2 EXP c) DIV 2 EXP b`,
  REPEAT STRIP_TAC
    THEN Cases_on `c <= b`
    THENL [
       POP_ASSUM (fn th => REWRITE_TAC [REWRITE_RULE [GSYM SUB_EQ_0] th,EXP,MOD_1]
                             THEN ASSUME_TAC (MATCH_MP TWOEXP_MONO2 th))
         THEN ASSUME_TAC (SPECL [`c`,`a`] MOD_2EXP_LT)
         THEN IMP_RES_TAC LESS_LESS_EQ_TRANS
         THEN ASM_B_SIMP_TAC [LESS_DIV_EQ_ZERO],
       RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS_EQUAL])
          THEN IMP_RES_TAC LESS_ADD
          THEN POP_ASSUM (fn th => A_SIMP_TAC [SYM th,DIV_MOD_MOD_DIV])
    ]
);

val BITS_THM2 = store_thm("BITS_THM2",
  `!h l n. BITS h l n = (n MOD 2 EXP SUC h) DIV 2 EXP l`,
  B_RW_TAC [BITS_THM,DIV_MOD_MOD_DIV2]
);

val BITS_COMP_LEM = prove(
  `!h1 l1 h2 l2 n. h2 + l1 <= h1 ==>
    (((n DIV 2 EXP l1) MOD 2 EXP (h1 - l1) DIV 2 EXP l2) MOD 2 EXP (h2 - l2) =
      (n DIV 2 EXP (l2 + l1)) MOD 2 EXP ((h2 + l1) - (l2 + l1)))`,
  REPEAT STRIP_TAC
    THEN REWRITE_TAC [SPECL [`(n DIV 2 EXP l1) MOD 2 EXP (h1 - l1)`,`l2`,`h2`] DIV_MOD_MOD_DIV2]
    THEN IMP_RES_TAC LESS_EQUAL_ADD
    THEN POP_ASSUM (fn th => A_SIMP_TAC [EXP_ADD,MOD_MULT_MOD,ZERO_LT_TWOEXP,th])
    THEN REWRITE_TAC [DIV_MOD_MOD_DIV]
    THEN A_SIMP_TAC [DIV_DIV_DIV_MULT,ZERO_LT_TWOEXP,GSYM EXP_ADD]
    THEN REWRITE_TAC [SIMP_RULE arith_ss [] (SPECL [`n`,`l1 + l2`,`h2 + l1`] DIV_MOD_MOD_DIV2)]
);

val BITS_COMP_THM = store_thm("BITS_COMP_THM",
  `!h1 l1 h2 l2 n. h2 + l1 <= h1 ==> (BITS h2 l2 (BITS h1 l1 n) = BITS (h2+l1) (l2+l1) n)`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_EQ_MONO
    THEN B_FULL_SIMP_TAC [BITS_THM,GSYM ADD_CLAUSES,BITS_COMP_LEM]
);

val BITS_DIV_THM = store_thm("BITS_DIV_THM",
  `!h l x n. (BITS h l x) DIV 2 EXP n = BITS h (l + n) x`,
  B_RW_TAC [BITS_THM2,EXP_ADD,ZERO_LT_TWOEXP,DIV_DIV_DIV_MULT]
);

val BITS_LT_HIGH = store_thm("BITS_LT_HIGH",
  `!h l n. n < 2 EXP SUC h ==> (BITS h l n = n DIV 2 EXP l)`,
  B_RW_TAC [BITS_THM2,LESS_MOD]
);

(* -------------------------------------------------------- *)

val BITS_ZERO = store_thm("BITS_ZERO",
  `!h l n. h < l ==> (BITS h l n = 0)`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_ADD_1
    THEN POP_ASSUM (fn th => REWRITE_TAC [th])
    THEN ASSUME_TAC ((REWRITE_RULE [EXP,SUB,SUB_EQUAL_0] o ONCE_REWRITE_RULE [SUB_PLUS] o
                        REWRITE_RULE [ADD1] o SPECL [`h`,`h + 1 + p`,`n`]) BITSLT_THM)
    THEN A_FULL_SIMP_TAC []
);

val BITS_ZERO2 = store_thm("BITS_ZERO2",
  `!h l. BITS h l 0 = 0`,
  B_RW_TAC [BITS_THM2,ZERO_MOD,ZERO_DIV,ZERO_LT_TWOEXP]
);

(* |- !h n. BITS h 0 n = n MOD 2 EXP SUC h *)
val BITS_ZERO3 = save_thm("BITS_ZERO3",
  (GEN_ALL o SIMP_RULE bool_ss [CONJUNCT1 EXP,DIV_1] o SPECL [`h`,`0`]) BITS_THM2
);

val BITS_ZERO4 = store_thm("BITS_ZERO4",
  `!h l n. l <= h ==> (BITS h l (a * 2 ** l) = BITS (h - l) 0 a)`,
  RW_TAC arith_ss [BITS_THM,MULT_DIV,ZERO_LT_TWOEXP,SUB]
);

val BITS_ZEROL = store_thm("BITS_ZEROL",
  `!h a. a < 2 EXP SUC h ==> (BITS h 0 a = a)`,
  RW_TAC bool_ss [BITS_ZERO3,LESS_MOD]
);

val BIT_ZERO = store_thm("BIT_ZERO",
  `!b. ~BIT b 0`,
  REWRITE_TAC [BIT_def,BITS_ZERO2,DECIDE ``~(0 = 1)``]
);

val BIT_B = store_thm("BIT_B",
  `!b. BIT b (2 EXP b)`,
  SIMP_TAC arith_ss [BIT_def,BITS_THM,DIVMOD_ID,ZERO_LT_TWOEXP,SUC_SUB]
);

val BIT_B_NEQ = store_thm("BIT_B_NEQ",
  `!a b. ~(a = b) ==> ~BIT a (2 EXP b)`,
  NTAC 3 STRIP_TAC
    THEN REWRITE_TAC [BIT_def,BITS_THM,SUC_SUB,EXP_1]
    THEN IMP_RES_TAC (DECIDE (Term `!(a:num) b. ~(a = b) ==> (a < b) \/ (b < a)`))
    THENL [
      IMP_RES_TAC LESS_ADD_1
        THEN ASM_SIMP_TAC arith_ss [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV,
                                    EXP_ADD,MOD_EQ_0,ZERO_LT_TWOEXP],
      IMP_RES_TAC TWOEXP_MONO THEN ASM_SIMP_TAC arith_ss [LESS_DIV_EQ_ZERO]
    ]
);

(* -------------------------------------------------------- *)

val BITS_COMP_THM2 = store_thm("BITS_COMP_THM2",
  `!h1 l1 h2 l2 n. BITS h2 l2 (BITS h1 l1 n) =
                   BITS (MIN h1 (h2 + l1)) (l2 + l1) n`,
  RW_TAC bool_ss [MIN_DEF,REWRITE_RULE [GSYM NOT_LESS] BITS_COMP_THM]
    THEN Cases_on `h2 = 0` THEN1 FULL_SIMP_TAC arith_ss [BITS_ZERO,BITS_ZERO2]
    THEN RULE_ASSUM_TAC (REWRITE_RULE [NOT_ZERO_LT_ZERO])
    THEN Cases_on `h1 < l1` THEN1 FULL_SIMP_TAC arith_ss [BITS_ZERO,BITS_ZERO2]
    THEN RULE_ASSUM_TAC (ONCE_REWRITE_RULE [ADD_COMM])
    THEN IMP_RES_TAC SUB_RIGHT_LESS
    THEN POP_ASSUM (fn th => ASSUME_TAC
           (MATCH_MP TWOEXP_MONO (ONCE_REWRITE_RULE [GSYM LESS_MONO_EQ] th)))
    THEN ASSUME_TAC (SPECL [`h1`,`l1`,`n`] BITSLT_THM)
    THEN Cases_on `h1 = l1`
    THENL [
      FULL_SIMP_TAC bool_ss [SUC_SUB, SUB_EQUAL_0, SYM ONE]
        THEN `BITS l1 l1 n < 2 ** SUC h2` by IMP_RES_TAC LESS_TRANS
        THEN ASM_SIMP_TAC arith_ss [BITS_LT_HIGH,BITS_DIV_THM],
      `~(h1 <= l1)` by DECIDE_TAC
        THEN POP_ASSUM (fn th => RULE_ASSUM_TAC
               (SIMP_RULE bool_ss [th,SUB_LEFT_SUC]))
        THEN `BITS h1 l1 n < 2 ** SUC h2` by IMP_RES_TAC LESS_TRANS
        THEN ASM_SIMP_TAC arith_ss [BITS_LT_HIGH,BITS_DIV_THM]]);

(* -------------------------------------------------------- *)

val NOT_MOD2_LEM = store_thm("NOT_MOD2_LEM",
  `!n. ~(n MOD 2 = 0) = (n MOD 2 = 1)`,
  A_RW_TAC [MOD_2]
);

val NOT_MOD2_LEM2 = store_thm("NOT_MOD2_LEM2",
  `!n a. ~(n MOD 2 = 1) = (n MOD 2 = 0)`,
  B_RW_TAC [GSYM NOT_MOD2_LEM]
);

val ODD_MOD2_LEM = store_thm("ODD_MOD2_LEM",
 `!n. ODD n = ((n MOD 2) = 1)`,
  A_RW_TAC [ODD_EVEN,MOD_2]
);

val BIT_OF_BITS_THM = Q.store_thm (
"BIT_OF_BITS_THM",
`!n h l a. l + n <= h ==> (BIT n (BITS h l a) = BIT (l + n) a)`,
RW_TAC arith_ss [BIT_def, BITS_COMP_THM]);

val BIT_SHIFT_THM = Q.store_thm (
"BIT_SHIFT_THM",
`!n a s. BIT (n + s) (a * 2 ** s) = BIT n a`,
RW_TAC std_ss [BIT_def, BITS_def,MOD_2EXP_def, DIV_2EXP_def] THEN
RW_TAC arith_ss [SUC_SUB, EXP_ADD] THEN
metisLib.METIS_TAC [GSYM DIV_DIV_DIV_MULT, ZERO_LT_TWOEXP,
                    MULT_DIV, MULT_SYM]);

val BIT_SHIFT_THM2 = Q.store_thm (
"BIT_SHIFT_THM2",
`!n a s. s <= n ==> (BIT n (a * 2 ** s) = BIT (n - s) a)`,
RW_TAC arith_ss [GSYM (Q.SPECL [`n-s`, `a`, `s`] BIT_SHIFT_THM)]);

val BIT_SHIFT_THM3 = Q.store_thm (
"BIT_SHIFT_THM3",
`!n a s. (n < s) ==> ~BIT n (a * 2 ** s)`,
RW_TAC std_ss [BIT_def, BITS_def,MOD_2EXP_def, DIV_2EXP_def] THEN
RW_TAC arith_ss [SUC_SUB, NOT_MOD2_LEM2, GSYM EVEN_MOD2] THEN
RW_TAC arith_ss [DIV_P, ZERO_LT_TWOEXP] THEN
Q.EXISTS_TAC `a * 2 ** (s - n)` THEN Q.EXISTS_TAC `0` THEN
RW_TAC arith_ss [ZERO_LT_TWOEXP,GSYM MULT_ASSOC, GSYM EXP_ADD, EVEN_MULT,
                 EVEN_EXP])

val BIT_OF_BITS_THM2 = store_thm("BIT_OF_BITS_THM2",
  `!h l x n.  h < l + x ==> ~BIT x (BITS h l n)`,
  RW_TAC arith_ss [MIN_DEF,BIT_def,BITS_COMP_THM2,BITS_ZERO]
);

(* -------------------------------------------------------- *)

val LSB_ODD = store_thm("LSB_ODD",
  `LSBn = ODD`,
  ONCE_REWRITE_TAC [FUN_EQ_THM]
    THEN A_SIMP_TAC [ODD_MOD2_LEM,LSBn_def,BIT_def,BITS_THM2,EXP,DIV_1]
);

(* -------------------------------------------------------- *)

val DIV_MULT_THM = store_thm("DIV_MULT_THM",
  `!x n. n DIV 2 EXP x * 2 EXP x = n - n MOD 2 EXP x`,
  A_RW_TAC [DIV_MULT_LESS_EQ,MOD_2EXP_LEM,SUB_SUB]
);

val DIV_MULT_THM2 = save_thm("DIV_MULT_THM2",
  ONCE_REWRITE_RULE [MULT_COMM] (REWRITE_RULE [EXP_1] (SPEC `1` DIV_MULT_THM))
);

val LESS_EQ_EXP_MULT = store_thm("LESS_EQ_EXP_MULT",
  `!a b. a <= b ==> ?p. 2 EXP b = p * 2 EXP a`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_EQUAL_ADD
    THEN EXISTS_TAC `2 EXP p`
    THEN FULL_SIMP_TAC arith_ss [EXP_ADD,MULT_COMM]
);

val LESS_EXP_MULT = SIMP_PROVE bool_ss [LESS_IMP_LESS_OR_EQ,LESS_EQ_EXP_MULT]
                      ``!a b. a < b ==> ?p. 2 EXP b = p * 2 EXP a``;

(* -------------------------------------------------------- *)

val SLICE_LEM1 = prove(
  `!a x y. a DIV 2 EXP (x + y) * 2 EXP (x + y) =
       a DIV 2 EXP x * 2 EXP x - (a DIV 2 EXP x) MOD 2 EXP y * 2 EXP x`,
  REPEAT STRIP_TAC
    THEN REWRITE_TAC [EXP_ADD]
    THEN SUBST_OCCS_TAC [([2],SPECL [`2 EXP x`,`2 EXP y`] MULT_COMM)]
    THEN B_SIMP_TAC [ZERO_LT_TWOEXP,GSYM DIV_DIV_DIV_MULT,MULT_ASSOC,
                     SPECL [`y`,`a DIV 2 EXP x`] DIV_MULT_THM,RIGHT_SUB_DISTRIB]
);

val SLICE_LEM2 = prove(
  `!a x y. n MOD 2 EXP (x + y) = n MOD 2 EXP x + (n DIV 2 EXP x) MOD 2 EXP y * 2 EXP x`,
  REPEAT STRIP_TAC
    THEN B_SIMP_TAC [DIV_MULT_LESS_EQ,MOD_2EXP_LEM,SLICE_LEM1,RIGHT_SUB_DISTRIB,SUB_SUB,SUB_LESS_EQ]
    THEN Cases_on `n = n DIV 2 EXP x * 2 EXP x` THEN1 POP_ASSUM (fn th => A_SIMP_TAC [SYM th])
    THEN ASSUME_TAC (REWRITE_RULE [GSYM NOT_LESS] DIV_MULT_LESS_EQ)
    THEN IMP_RES_TAC LESS_CASES_IMP
    THEN B_RW_TAC [SUB_RIGHT_ADD]
    THEN PROVE_TAC [GSYM NOT_LESS_EQUAL]
);

val SLICE_LEM3 = prove(
  `!n h l. l < h ==> n MOD 2 EXP SUC l <= n MOD 2 EXP h`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_ADD_1
    THEN POP_ASSUM (fn th => REWRITE_TAC [th])
    THEN REWRITE_TAC [GSYM ADD1,GSYM ADD_SUC,GSYM (CONJUNCT2 ADD)]
    THEN A_SIMP_TAC [SLICE_LEM2]
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
        THEN ASM_SIMP_TAC arith_ss [EXP,MOD_1,MULT_CLAUSES],
      REWRITE_TAC [DIV_MOD_MOD_DIV2]
        THEN RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS])
        THEN SUBST_OCCS_TAC [([1],SPECL [`l`,`n MOD 2 EXP SUC h`] TWOEXP_DIVISION)]
        THEN IMP_RES_TAC LESS_EQUAL_ADD
        THEN POP_ASSUM (fn th => SUBST_OCCS_TAC [([2],th)])
        THEN B_SIMP_TAC [ADD_SUC,ADD_SUB,MOD_MULT_MOD,ZERO_LT_TWOEXP,EXP_ADD]
    ]
);

val SLICELT_THM = store_thm("SLICELT_THM",
  `!h l n. SLICE h l n < 2 EXP SUC h`,
  REPEAT STRIP_TAC
    THEN ASSUME_TAC (SPECL [`SUC h`,`n`] MOD_2EXP_LT)
    THEN A_RW_TAC [SLICE_def,MOD_2EXP_def,ZERO_LT_TWOEXP,SUB_RIGHT_LESS]
);

val BITS_SLICE_THM = store_thm("BITS_SLICE_THM",
  `!h l n. BITS h l (SLICE h l n) = BITS h l n`,
  B_RW_TAC [SLICELT_THM,BITS_LT_HIGH,ZERO_LT_TWOEXP,SLICE_THM,MULT_DIV]
);

val BITS_SLICE_THM2 = store_thm("BITS_SLICE_THM2",
  `!h l n. h <= h2 ==> (BITS h2 l (SLICE h l n) = BITS h l n)`,
  REPEAT STRIP_TAC
    THEN LEFT_REWRITE_TAC [BITS_THM]
    THEN B_SIMP_TAC [SLICE_THM,ZERO_LT_TWOEXP,MULT_DIV]
    THEN `SUC h - l <= SUC h2 - l` by DECIDE_TAC
    THEN IMP_RES_TAC TWOEXP_MONO2 THEN POP_ASSUM (K ALL_TAC)
    THEN ASSUME_TAC (SPECL [`h`,`l`,`n`] BITSLT_THM)
    THEN IMP_RES_TAC LESS_LESS_EQ_TRANS
    THEN ASM_B_SIMP_TAC [LESS_MOD]
);

val SLICE_ZERO_THM = save_thm("SLICE_ZERO_THM",
  (GEN_ALL o REWRITE_RULE [MULT_RIGHT_1,EXP] o SPECL [`n`,`h`,`0`]) SLICE_THM
);

val MOD_2EXP_MONO = store_thm("MOD_2EXP_MONO",
  `!n h l. l <= h ==> n MOD 2 EXP l <= n MOD 2 EXP SUC h`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_EQ_EXISTS
    THEN ASM_A_SIMP_TAC [SUC_ADD_SYM,SLICE_LEM2]
);

val SLICE_COMP_THM = store_thm("SLICE_COMP_THM",
  `!h m l n. (SUC m) <= h /\ l <= m ==> (SLICE h (SUC m) n + SLICE m l n = SLICE h l n)`,
  B_RW_TAC [SLICE_def,MOD_2EXP_def,MOD_2EXP_MONO,GSYM LESS_EQ_ADD_SUB,SUB_ADD]
);

val SLICE_COMP_RWT = store_thm("SLICE_COMP_RWT",
  `!h m' m l n. l <= m /\ (m' = m + 1) /\ m < h ==>
             (SLICE h m' n + SLICE m l n = SLICE h l n)`,
  A_RW_TAC [SLICE_COMP_THM,GSYM ADD1]
);

val SLICE_ZERO = store_thm("SLICE_ZERO",
  `!h l n. h < l ==> (SLICE h l n = 0)`,
  A_RW_TAC [SLICE_THM,BITS_ZERO]
);

(* -------------------------------------------------------- *)

val BITS_SUM = store_thm("BITS_SUM",
  `!h l a b. b < 2 ** l ==> (BITS h l (a * 2 ** l + b) = BITS h l (a * 2 ** l))`,
  RW_TAC bool_ss [BITS_THM,DIV_MULT,MULT_DIV,ZERO_LT_TWOEXP]
);

val BITS_SUM2 = store_thm("BITS_SUM2",
  `!h l a b. BITS h l (a * 2 ** SUC h + b) = BITS h l b`,
  RW_TAC bool_ss [BITS_THM2,MOD_TIMES,ZERO_LT_TWOEXP]
);

val SLICE_TWOEXP = prove(
  `!h l a n. SLICE (h + n) (l + n) (a * 2 ** n) = (SLICE h l a) * 2 ** n`,
  REPEAT STRIP_TAC
    THEN SUBST1_TAC (SPECL [`l`,`n`] ADD_COMM)
    THEN RW_TAC bool_ss [(GSYM o CONJUNCT2) ADD,SLICE_THM,BITS_THM,MULT_DIV,EXP_ADD,GSYM DIV_DIV_DIV_MULT,ZERO_LT_TWOEXP]
    THEN SIMP_TAC arith_ss [AC MULT_ASSOC MULT_COMM]
);

val SPEC_SLICE_TWOEXP =
  (GEN_ALL o SIMP_RULE arith_ss [] o DISCH `n <= l /\ n <= h` o SPECL [`h - n`,`l - n`,`a`,`n`]) SLICE_TWOEXP;

val SLICE_COMP_THM2 = store_thm("SLICE_COMP_THM2",
  `!h l x y n.
      h <= x /\ y <= l ==>
        (SLICE h l (SLICE x y n) = SLICE h l n)`,
  REPEAT STRIP_TAC
    THEN Cases_on `h < l` THEN1 ASM_SIMP_TAC bool_ss [SLICE_ZERO]
    THEN `y <= h` by DECIDE_TAC
    THEN SUBST1_TAC (SPECL [`n`,`x`,`y`] SLICE_THM)
    THEN ASM_SIMP_TAC bool_ss [SPEC_SLICE_TWOEXP]
    THEN ASM_SIMP_TAC arith_ss [SLICE_THM,BITS_COMP_THM2,MIN_DEF]
    THEN SIMP_TAC bool_ss [GSYM MULT_ASSOC,GSYM EXP_ADD]
    THEN ASM_SIMP_TAC arith_ss []
);

(* -------------------------------------------------------- *)

val lem  = prove(`!c a b. (a = b) ==> (a DIV c = b DIV c)`, A_RW_TAC []);
val lem2 = prove(`!a b c. a * (b * c) = a * c * b`,
                 SIMP_TAC arith_ss [AC MULT_ASSOC MULT_COMM]);

val lem3 = prove(
  `!a m n. n <= m ==> (a * 2 EXP m DIV 2 EXP n = a * 2 EXP (m - n))`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_EQUAL_ADD
    THEN ASM_SIMP_TAC arith_ss [EXP_ADD,MULT_DIV,ZERO_LT_TWOEXP,lem2]
);

(* |- !a m n. n < m ==> (a * 2 EXP m DIV 2 EXP n = a * 2 EXP (m - n)) *)
val lem4 = SIMP_PROVE std_ss [LESS_IMP_LESS_OR_EQ,lem3]
             ``!a m n. n < m ==> (a * 2 EXP m DIV 2 EXP n = a * 2 EXP (m - n))``;

val BIT_COMP_THM3 = store_thm("BIT_COMP_THM3",
  `!h m l n.  SUC m <= h /\ l <= m ==>
         (BITS h (SUC m) n * 2 EXP (SUC m - l) + BITS m l n = BITS h l n)`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC (REWRITE_RULE [SLICE_THM] SLICE_COMP_THM)
    THEN POP_ASSUM (K ALL_TAC)
    THEN POP_ASSUM (fn th => ASSUME_TAC (GEN `l'` (MATCH_MP (SPEC `2 EXP l` lem) (SPEC `n` th))))
    THEN POP_ASSUM (fn th => ASSUME_TAC (ONCE_REWRITE_RULE [ADD_COMM] (SPEC `l` th)))
    THEN `l < SUC m` by ASM_A_SIMP_TAC []
    THEN A_FULL_SIMP_TAC [lem4,ADD_DIV_ADD_DIV,MULT_DIV,ZERO_LT_TWOEXP]
);

(* -------------------------------------------------------- *)

val BITS_SUM = store_thm("BITS_SUM",
  `!h l a b. b < 2 ** l ==> (BITS h l (a * 2 ** l + b) = BITS h l (a * 2 ** l))`,
  RW_TAC bool_ss [BITS_THM,DIV_MULT,MULT_DIV,ZERO_LT_TWOEXP]
);

val BITS_SUM2 = store_thm("BITS_SUM2",
  `!h l a b. BITS h l (a * 2 ** SUC h + b) = BITS h l b`,
  RW_TAC bool_ss [BITS_THM2,MOD_TIMES,ZERO_LT_TWOEXP]
);

val SLICE_TWOEXP = prove(
  `!h l a n. SLICE (h + n) (l + n) (a * 2 ** n) = (SLICE h l a) * 2 ** n`,
  REPEAT STRIP_TAC
    THEN SUBST1_TAC (SPECL [`l`,`n`] ADD_COMM)
    THEN RW_TAC bool_ss [(GSYM o CONJUNCT2) ADD,SLICE_THM,BITS_THM,MULT_DIV,EXP_ADD,GSYM DIV_DIV_DIV_MULT,ZERO_LT_TWOEXP]
    THEN SIMP_TAC arith_ss [AC MULT_ASSOC MULT_COMM]
);

val SPEC_SLICE_TWOEXP =
  (GEN_ALL o SIMP_RULE arith_ss [] o DISCH `n <= l /\ n <= h` o SPECL [`h - n`,`l - n`,`a`,`n`]) SLICE_TWOEXP;

val SLICE_COMP_THM2 = store_thm("SLICE_COMP_THM2",
  `!h l x y n.
      h <= x /\ y <= l ==>
        (SLICE h l (SLICE x y n) = SLICE h l n)`,
  REPEAT STRIP_TAC
    THEN Cases_on `h < l` THEN1 ASM_SIMP_TAC bool_ss [SLICE_ZERO]
    THEN `y <= h` by DECIDE_TAC
    THEN SUBST1_TAC (SPECL [`n`,`x`,`y`] SLICE_THM)
    THEN ASM_SIMP_TAC bool_ss [SPEC_SLICE_TWOEXP]
    THEN ASM_SIMP_TAC arith_ss [SLICE_THM,BITS_COMP_THM2,MIN_DEF]
    THEN SIMP_TAC bool_ss [GSYM MULT_ASSOC,GSYM EXP_ADD]
    THEN ASM_SIMP_TAC arith_ss []
);

(* -------------------------------------------------------- *)

val NOT_BIT = store_thm("NOT_BIT",
  `!n a. ~BIT n a = (BITS n n a = 0)`,
  B_RW_TAC [BIT_def,BITS_THM,SUC_SUB,EXP_1,GSYM NOT_MOD2_LEM]
);

val NOT_BITS = store_thm("NOT_BITS",
  `!n a. ~(BITS n n a = 0) = (BITS n n a = 1)`,
  B_RW_TAC [GSYM NOT_BIT,GSYM BIT_def]
);

val NOT_BITS2 = store_thm("NOT_BITS2",
  `!n a. ~(BITS n n a = 1) = (BITS n n a = 0)`,
  B_RW_TAC [GSYM NOT_BITS]
);

val BIT_SLICE = store_thm("BIT_SLICE",
  `!n a b. (BIT n a = BIT n b) = (SLICE n n a = SLICE n n b)`,
  REPEAT STRIP_TAC THEN EQ_TAC
    THENL [
      Cases_on `BIT n a`
        THEN A_FULL_SIMP_TAC [BIT_def,SLICE_THM,NOT_BITS2],
      Cases_on `BITS n n a = 1`
        THEN Cases_on `BITS n n b = 1`
        THEN A_FULL_SIMP_TAC [BIT_def,SLICE_THM,NOT_BITS2,MULT_CLAUSES,
                              REWRITE_RULE [GSYM NOT_ZERO_LT_ZERO] ZERO_LT_TWOEXP]
    ]
);

val BIT_SLICE_LEM = store_thm("BIT_SLICE_LEM",
  `!y x n. SBIT (BIT x n) (x + y) = (SLICE x x n) * 2 EXP y`,
  A_RW_TAC [SBIT_def,BIT_SLICE,SLICE_THM,BIT_def,EXP_ADD]
    THEN B_FULL_SIMP_TAC [GSYM NOT_BITS]
);

(* |- !x n. SBIT (BIT x n) x = SLICE x x n *)
val BIT_SLICE_THM = save_thm("BIT_SLICE_THM",
   SIMP_RULE arith_ss [EXP] (SPEC `0` BIT_SLICE_LEM)
);

val BIT_SLICE_THM2 = store_thm("BIT_SLICE_THM2",
  `!b n. BIT b n = (SLICE b b n = 2 EXP b)`,
  RW_TAC bool_ss [SBIT_def,GSYM BIT_SLICE_THM,TWOEXP_NOT_ZERO]
);

val BIT_SLICE_THM3 = store_thm("BIT_SLICE_THM3",
  `!b n. ~BIT b n = (SLICE b b n = 0)`,
  RW_TAC bool_ss [SBIT_def,GSYM BIT_SLICE_THM,TWOEXP_NOT_ZERO]
);

val SUB_BITS = prove(
  `!h l a b. (BITS (SUC h) l a = BITS (SUC h) l b) ==> (BITS h l a = BITS h l b)`,
  REPEAT STRIP_TAC
    THEN Cases_on `h < l` THEN1 B_RW_TAC [BITS_ZERO]
    THEN RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS])
    THEN POP_ASSUM (fn th => ONCE_REWRITE_TAC [(GSYM o SIMP_RULE arith_ss [th,SUB_ADD] o
                                        SPECL [`SUC h`,`l`,`h - l`,`0`]) BITS_COMP_THM])
    THEN ASM_REWRITE_TAC []
);

val SBIT_DIV = store_thm("SBIT_DIV",
  `!b m n. n < m ==> (SBIT b (m - n) = SBIT b m DIV 2 EXP n)`,
  B_RW_TAC [SBIT_def,ZERO_DIV,ZERO_LT_TWOEXP,SIMP_RULE arith_ss [] (SPEC `1` lem4)]
);

val BITS_SUC = store_thm("BITS_SUC",
  `!h l n.  l <= SUC h ==>
         (SBIT (BIT (SUC h) n) (SUC h - l) + BITS h l n = BITS (SUC h) l n)`,
  REPEAT STRIP_TAC
    THEN Cases_on `l = SUC h`
    THENL [
      A_RW_TAC [EXP,BITS_ZERO,SBIT_def,BIT_def]
        THEN B_FULL_SIMP_TAC [NOT_BITS2],
      `l <= h` by ASM_A_SIMP_TAC []
        THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
        THEN ASM_A_SIMP_TAC [SBIT_DIV,BIT_SLICE_THM,SLICE_THM,lem4,SPECL [`SUC h`,`h`] BIT_COMP_THM3]
    ]
);

val BITS_SUC_THM = store_thm("BITS_SUC_THM",
  `!h l n. BITS (SUC h) l n =
             if SUC h < l then 0 else SBIT (BIT (SUC h) n) (SUC h - l) + BITS h l n`,
  A_RW_TAC [BITS_ZERO,BITS_SUC]
);

val DECEND_LEMMA = prove(
  `!P l y.  (!x. l <= x /\ x <= SUC y ==> P x) ==> (!x. l <= x /\ x <= y ==> P x)`,
  A_RW_TAC []
);

val BIT_BITS_LEM = prove(
  `!h l a b. l <= h ==> (BITS h l a = BITS h l b) ==> (BIT h a = BIT h b)`,
  B_RW_TAC [BIT_SLICE,SLICE_THM]
    THEN PAT_ASSUM `l <= h`
           (fn th => ONCE_REWRITE_TAC [(GSYM o SIMP_RULE arith_ss [th,SUB_ADD] o
                                        SPECL [`h`,`l`,`h - l`,`h - l`]) BITS_COMP_THM])
    THEN ASM_REWRITE_TAC []
);

val BIT_BITS_THM = store_thm("BIT_BITS_THM",
  `!h l a b. (!x. l <= x /\ x <= h ==> (BIT x a = BIT x b)) = (BITS h l a = BITS h l b)`,
  Induct_on `h`
    THEN REPEAT STRIP_TAC
    THENL [
      Cases_on `l = 0`
        THEN A_RW_TAC [BIT_SLICE,SLICE_THM,EXP,SPEC `0` BITS_ZERO,NOT_ZERO_LT_ZERO],
      EQ_TAC THEN REPEAT STRIP_TAC
        THENL [
          B_RW_TAC [BITS_SUC_THM]
            THEN RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS])
            THEN PAT_ASSUM `!x. l <= x /\ x <= SUC h ==> (BIT x a = BIT x b)`
                   (fn th => ASM_B_SIMP_TAC [SIMP_RULE arith_ss [] (SPEC `SUC h` th)]
                       THEN ASSUME_TAC (MATCH_MP
                                 ((BETA_RULE o SPECL [`\x. BIT x a = BIT x b`,`l`,`h`]) DECEND_LEMMA) th))
            THEN FIRST_ASSUM (fn th => ASSUME_TAC (SPECL [`l`,`a`,`b`] th))
            THEN B_FULL_SIMP_TAC [],
          IMP_RES_TAC SUB_BITS
            THEN FIRST_ASSUM (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM (SPECL [`l`,`a`,`b`] th)]))
            THEN Cases_on `x <= h`
            THEN ASM_B_SIMP_TAC []
            THEN `x = SUC h` by ASM_A_SIMP_TAC []
            THEN Cases_on `l = SUC h` THEN1 B_FULL_SIMP_TAC [BIT_def]
            THEN `l <= SUC h` by ASM_A_SIMP_TAC []
            THEN POP_ASSUM (fn th =>
                       ASSUME_TAC (SIMP_RULE bool_ss [th] (SPECL [`SUC h`,`l`,`a`,`b`] BIT_BITS_LEM)))
            THEN B_FULL_SIMP_TAC []
        ]
    ]
);

(* -------------------------------------------------------- *)

val BITV_THM = store_thm("BITV_THM",
  `!b n. BITV n b = SBIT (BIT b n) 0`,
  RW_TAC arith_ss [BITV_def,BIT_def,SBIT_def]
    THEN FULL_SIMP_TAC bool_ss [NOT_BITS2]
);

(* -------------------------------------------------------- *)

val BITWISE_LT_2EXP = store_thm("BITWISE_LT_2EXP",
  `!n op a b. BITWISE n op a b < 2 EXP n`,
  Induct_on `n`
    THEN B_RW_TAC [ADD_0,TIMES2,LESS_IMP_LESS_ADD,LESS_MONO_ADD,BITWISE_def,SBIT_def,EXP]
    THEN REDUCE_TAC
);

val LESS_EXP_MULT2 = prove(
  `!a b. a < b ==> ?p. 2 EXP b = 2 EXP (p + 1) * 2 EXP a`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_ADD_1
    THEN EXISTS_TAC `p`
    THEN FULL_SIMP_TAC arith_ss [EXP_ADD]
);

val BITWISE_LEM = prove(
  `!n op a b. BIT n (BITWISE (SUC n) op a b) = op (BIT n a) (BIT n b)`,
  A_RW_TAC [SBIT_def,BITWISE_def,NOT_BIT]
    THENL [
       A_SIMP_TAC [BIT_def,BITS_THM,SUC_SUB,
                  REWRITE_RULE [BITWISE_LT_2EXP] (SPECL [`BITWISE n op a b`,`2 EXP n`] DIV_MULT_1)],
       A_SIMP_TAC [BITS_THM,LESS_DIV_EQ_ZERO,BITWISE_LT_2EXP,SUC_SUB]
    ]
);

val TWO_SUC_SUB = GEN_ALL (SIMP_CONV bool_ss [SUC_SUB,EXP_1] ``2 EXP (SUC x - x)``);

val BITWISE_THM = store_thm("BITWISE_THM",
  `!x n op a b. x < n ==> (BIT x (BITWISE n op a b) = op (BIT x a) (BIT x b))`,
  Induct_on `n`
    THEN REPEAT STRIP_TAC THEN1 A_FULL_SIMP_TAC []
    THEN Cases_on `x = n` THEN1 ASM_REWRITE_TAC [BITWISE_LEM]
    THEN `x < n` by ASM_A_SIMP_TAC []
    THEN A_RW_TAC [BITWISE_def,SBIT_def]
    THEN LEFT_REWRITE_TAC [BIT_def]
    THEN ASM_REWRITE_TAC [BITS_THM]
    THEN IMP_RES_TAC LESS_EXP_MULT2
    THEN POP_ASSUM (K ALL_TAC)
    THEN ASM_B_SIMP_TAC [ZERO_LT_TWOEXP,ADD_DIV_ADD_DIV,TWO_SUC_SUB,GSYM ADD1,EXP,
           ONCE_REWRITE_RULE [MULT_COMM] (REWRITE_RULE [DECIDE (Term `0 < 2`)] (SPEC `2` MOD_TIMES))]
    THEN SUBST_OCCS_TAC [([2],SYM (SPEC `x` TWO_SUC_SUB))]
    THEN ASM_B_SIMP_TAC [GSYM BITS_THM,GSYM BIT_def]
);

val BITWISE_COR = store_thm("BITWISE_COR",
  `!x n op a b. x < n ==> op (BIT x a) (BIT x b) ==> ((BITWISE n op a b DIV 2 EXP x) MOD 2 = 1)`,
  NTAC 6 STRIP_TAC
    THEN IMP_RES_TAC BITWISE_THM
    THEN NTAC 2 (WEAKEN_TAC (K true))
    THEN POP_ASSUM (fn th => REWRITE_TAC [GSYM th])
    THEN ASM_REWRITE_TAC [BITS_THM,BIT_def,DIV_1,EXP_1,SUC_SUB]
);

val BITWISE_NOT_COR = store_thm("BITWISE_NOT_COR",
  `!x n op a b. x < n ==> ~op (BIT x a) (BIT x b) ==> ((BITWISE n op a b DIV 2 EXP x) MOD 2 = 0)`,
  NTAC 6 STRIP_TAC
    THEN IMP_RES_TAC BITWISE_THM
    THEN NTAC 2 (WEAKEN_TAC (K true))
    THEN POP_ASSUM (fn th => REWRITE_TAC [GSYM th])
    THEN ASM_REWRITE_TAC [BITS_THM,BIT_def,GSYM NOT_MOD2_LEM,DIV_1,EXP_1,SUC_SUB]
);

val BITWISE_BITS = store_thm("BITWISE_BITS",
  `!wl op a b. BITWISE (SUC wl) op (BITS wl 0 a) (BITS wl 0 b) = BITWISE (SUC wl) op a b`,
  Induct
    THEN SIMP_TAC arith_ss [BITWISE_def,BIT_def,BITS_COMP_THM2,MIN_DEF]
    THEN FULL_SIMP_TAC arith_ss [BITWISE_def,BIT_def,BITS_COMP_THM2,MIN_DEF]
    THEN POP_ASSUM (fn th => ONCE_REWRITE_TAC [GSYM th])
    THEN SIMP_TAC arith_ss [BITS_COMP_THM2,MIN_DEF]
);

(* -------------------------------------------------------- *)

val BITS_SUC2 = prove(
  `!n a. BITS (SUC n) 0 a = SLICE (SUC n) (SUC n) a + BITS n 0 a`,
  A_RW_TAC [GSYM SLICE_ZERO_THM,SLICE_COMP_THM]
);

val lem = prove(
  `!n a. a < 2 EXP SUC n ==> ~(2 EXP SUC n < a + 1)`,
  A_RW_TAC [NOT_LESS,EXP]
);

val lem2 = MATCH_MP lem (REWRITE_RULE [SUB_0] (SPECL [`n`,`0`,`a`] BITSLT_THM));

val BITWISE_ONE_COMP_LEM = store_thm("BITWISE_ONE_COMP_LEM",
  `!n a b. BITWISE (SUC n) (\x y. ~x) a b = 2 EXP (SUC n) - 1 - BITS n 0 a`,
  Induct_on `n`
    THEN REPEAT STRIP_TAC THEN1 A_RW_TAC [SBIT_def,BIT_def,BITWISE_def,NOT_BITS2]
    THEN A_RW_TAC [BITWISE_def,SBIT_def,REWRITE_RULE [SLICE_THM] BITS_SUC2]
    THEN RULE_ASSUM_TAC (SIMP_RULE bool_ss [NOT_BIT,NOT_BITS,BIT_def])
    THEN ASM_A_SIMP_TAC [MULT_CLAUSES]
    THENL [
      Cases_on `2 EXP SUC n = BITS n 0 a + 1` THEN1 ASM_A_SIMP_TAC [SUB_RIGHT_ADD,EXP]
        THEN ASSUME_TAC lem2
        THEN `~(2 EXP SUC n <= BITS n 0 a + 1)` by ASM_A_SIMP_TAC []
        THEN ASM_A_SIMP_TAC [SUB_RIGHT_ADD,EXP],
      REWRITE_TAC [REWRITE_CONV [ADD_SUB,TIMES2] (Term`2 * a - a`),SUB_PLUS,EXP]
    ]
);

(* -------------------------------------------------------- *)

val BIT_SET_NOT_ZERO = prove(
  `!a. (a MOD 2 = 1) ==> (1 <= a)`,
  SPOSE_NOT_THEN STRIP_ASSUME_TAC
    THEN `a = 0` by DECIDE_TAC
    THEN A_FULL_SIMP_TAC [ZERO_MOD]
);

val BIT_SET_NOT_ZERO_COR = prove(
  `!x n op a b. x < n ==> op (BIT x a) (BIT x b) ==> (1 <= (BITWISE n op a b DIV 2 EXP x))`,
  REPEAT STRIP_TAC THEN ASM_B_SIMP_TAC [BITWISE_COR,BIT_SET_NOT_ZERO]
);

val BIT_SET_NOT_ZERO_COR2 = REWRITE_RULE [DIV_1,EXP] (SPEC `0` BIT_SET_NOT_ZERO_COR);

val ADD_DIV_ADD_DIV2 = ONCE_REWRITE_RULE [MULT_COMM] (SIMP_RULE arith_ss [] (SPEC `2` ADD_DIV_ADD_DIV));

val BIT_DIV2 = prove(
  `!i. BIT n (i DIV 2) = BIT (SUC n) i`,
  A_RW_TAC [BIT_def,BITS_THM,EXP,ZERO_LT_TWOEXP,DIV_DIV_DIV_MULT]
);

val SBIT_MULT = store_thm("SBIT_MULT",
  `!b m n. (SBIT b n) * 2 ** m = SBIT b (n + m)`,
  RW_TAC arith_ss [SBIT_def,EXP_ADD]
);

val lemma1 = prove(
  `!a b n. 0 < n ==> ((a + SBIT b n) DIV 2 = a DIV 2 + SBIT b (n - 1))`,
  A_RW_TAC [SBIT_def]
    THEN IMP_RES_TAC LESS_ADD_1
    THEN A_FULL_SIMP_TAC [GSYM ADD1,ADD_DIV_ADD_DIV2,EXP]
);

val lemma2 = (ONCE_REWRITE_RULE [MULT_COMM] o REWRITE_RULE [EXP_1] o
              INST [`m` |-> `1`] o SPEC_ALL) SBIT_MULT;

val lemma3 = prove(
  `!n op a b. 0 < n ==> (BITWISE n op a b MOD 2 = SBIT (op (LSBn a) (LSBn b)) 0)`,
  B_RW_TAC [LSBn_def]
    THEN POP_ASSUM (fn th => ONCE_REWRITE_TAC [MATCH_MP ((GSYM o SPEC `0`) BITWISE_THM) th])
    THEN B_RW_TAC [GSYM LSBn_def,LSB_ODD,ODD_MOD2_LEM,SBIT_def,EXP]
    THEN B_FULL_SIMP_TAC [GSYM NOT_MOD2_LEM]
);

val lemma4 = prove(
  `!n op a b. 0 < n /\ BITWISE n op a b <= SBIT (op (LSBn a) (LSBn b)) 0 ==>
              (BITWISE n op a b = SBIT (op (LSBn a) (LSBn b)) 0)`,
  A_RW_TAC [LSBn_def,SBIT_def,EXP]
    THEN IMP_RES_TAC BIT_SET_NOT_ZERO_COR2
    THEN ASM_A_SIMP_TAC []
);

val BITWISE_ISTEP = prove(
  `!n op a b. 0 < n ==> (BITWISE n op (a DIV 2) (b DIV 2) =
                        (BITWISE n op a b) DIV 2 + SBIT (op (BIT n a) (BIT n b)) (n - 1))`,
  Induct_on `n`
    THEN REPEAT STRIP_TAC THEN1 A_FULL_SIMP_TAC []
    THEN Cases_on `n = 0` THEN1 A_RW_TAC [BITWISE_def,SBIT_def,BIT_DIV2]
    THEN B_FULL_SIMP_TAC [NOT_ZERO_LT_ZERO,BITWISE_def,SUC_SUB1,BIT_DIV2,lemma1]
);

val BITWISE_EVAL = store_thm("BITWISE_EVAL",
  `!n op a b. BITWISE (SUC n) op a b =
         2 * (BITWISE n op (a DIV 2) (b DIV 2)) + SBIT (op (LSBn a) (LSBn b)) 0`,
  REPEAT STRIP_TAC
    THEN Cases_on `n = 0` THEN1 A_RW_TAC [BITWISE_def,MULT_CLAUSES,LSBn_def]
    THEN A_FULL_SIMP_TAC [BITWISE_def,NOT_ZERO_LT_ZERO,BITWISE_ISTEP,DIV_MULT_THM2,
                          LEFT_ADD_DISTRIB,SUB_ADD,lemma2,lemma3]
    THEN A_RW_TAC [SUB_RIGHT_ADD,lemma4]
);

(* -------------------------------------------------------- *)

val MOD_PLUS_RIGHT = store_thm("MOD_PLUS_RIGHT",
 `!n. 0<n ==> !j k. ((j + (k MOD n)) MOD n) = ((j+k) MOD n)`,
   let fun SUBS th = SUBST_OCCS_TAC [([2],th)]
   in
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC MOD_TIMES THEN
   PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
   IMP_RES_THEN (TRY o SUBS o SPEC (`k:num`)) DIVISION THEN
   ASM_REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC)]
   end);

val MOD_LESS = prove(
  `!n a. 0 < n ==> a MOD n < n`,
  PROVE_TAC [DIVISION]
);

val MOD_LESS1 = prove(
  `!n. 0 < n ==> a MOD n + 1 <= n`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC MOD_LESS
    THEN POP_ASSUM (fn th => ASSUME_TAC (SPEC `a` th))
    THEN A_RW_TAC []
);

val MOD_ZERO = prove(
  `!n. 0 < n /\ 0 < a /\ a <= n /\ (a MOD n = 0) ==> (a = n)`,
  REPEAT STRIP_TAC
    THEN Cases_on `a < n`
    THEN A_FULL_SIMP_TAC [LESS_MOD,GSYM NOT_ZERO_LT_ZERO]
);

val MOD_PLUS_1 = store_thm("MOD_PLUS_1",
  `!n. 0 < n ==> !x. ((x + 1) MOD n = 0) = (x MOD n + 1 = n)`,
  REPEAT STRIP_TAC
    THEN Cases_on `n = 1` THEN1 ASM_A_SIMP_TAC [MOD_1]
    THEN IMP_RES_TAC MOD_PLUS
    THEN POP_ASSUM (fn th => ONCE_REWRITE_TAC [GSYM th])
    THEN `1 < n` by ASM_A_SIMP_TAC []
    THEN ASM_B_SIMP_TAC [LESS_MOD]
    THEN EQ_TAC THEN STRIP_TAC
    THENL [
      `0 < x MOD n + 1` by A_SIMP_TAC []
        THEN IMP_RES_TAC MOD_LESS1
        THEN POP_ASSUM (fn th => ASSUME_TAC (SPEC `x` th))
        THEN IMP_RES_TAC MOD_ZERO,
      ASM_B_SIMP_TAC [ADD_EQ_SUB,SUB_ADD,DIVMOD_ID]
    ]
);

val MOD_ADD_1 = store_thm("MOD_ADD_1",
  `!n. 0 < n ==> !x. ~((x + 1) MOD n = 0) ==> ((x + 1) MOD n = x MOD n + 1)`,
  B_RW_TAC [MOD_PLUS_1]
    THEN IMP_RES_TAC (SPEC `n` DIVISION)
    THEN PAT_ASSUM `!k. k = k DIV n * n + k MOD n` (fn th => SUBST_OCCS_TAC [([1],SPEC `x` th)])
    THEN ONCE_REWRITE_TAC [GSYM ADD_ASSOC]
    THEN POP_ASSUM (fn th => ASSUME_TAC (SPEC `x` th))
    THEN `x MOD n + 1 < n` by ASM_A_SIMP_TAC []
    THEN ASM_B_SIMP_TAC [MOD_TIMES,LESS_MOD]

);

(* -------------------------------------------------------- *)

val TWO_EXP_GEQ_1 = (numLib.REDUCE_RULE o SPEC `0`) TWOEXP_MONO2;

val LOG2_THM = store_thm("LOG2_THM",
  `!n. 0 < n ==> ?q. n = 2 ** q + n MOD 2 ** q`,
  Induct THEN RW_TAC arith_ss []
    THEN Cases_on `n`
    THEN FULL_SIMP_TAC arith_ss []
    THEN1 (EXISTS_TAC `0` THEN SIMP_TAC arith_ss [])
    THEN EXISTS_TAC `if SUC n' MOD 2 ** q = 2 ** q - 1 then q + 1 else q`
    THEN RW_TAC std_ss []
    THENL [
       POP_ASSUM SUBST_ALL_TAC
         THEN ASM_SIMP_TAC (arith_ss++numSimps.ARITH_AC_ss)
                [ZERO_LT_TWOEXP,EXP_ADD,DECIDE ``!n. 0 < n ==> (SUC (n - 1) = n)``],
       `~(SUC (SUC n') MOD 2 ** q = 0)` by
          (FULL_SIMP_TAC std_ss [ZERO_LT_TWOEXP,MOD_PLUS_1,ADD1,TWO_EXP_GEQ_1]
            THEN FULL_SIMP_TAC arith_ss [])
        THEN ABBREV_TAC `n = SUC n'`
        THEN FULL_SIMP_TAC arith_ss [ZERO_LT_TWOEXP,MOD_ADD_1,ADD1]
    ]
);

val LOG2_exists = prove(
  `?LOG2. !n. 0 < n ==> (n = 2 ** (LOG2 n) + n MOD 2 ** (LOG2 n))`,
  EXISTS_TAC `\n. @q. n = 2 ** q + n MOD (2 ** q)`
    THEN RW_TAC std_ss []
    THEN SELECT_ELIM_TAC
    THEN RW_TAC std_ss [LOG2_THM]
);

val LOG2 = new_specification ("LOG2", ["LOG2"], LOG2_exists);

val LOG2_LBOUND = prove(
  `!m. 0 < m ==> 2 ** LOG2 m <= m`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC LOG2 THEN
  POP_ASSUM (fn th => CONV_TAC (RAND_CONV (K th))) THEN DECIDE_TAC)

val LOG2_UBOUND = prove(
  `!m. 0 < m ==> m < 2 ** (LOG2 m + 1)`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC LOG2 THEN
  POP_ASSUM (fn th => CONV_TAC (LAND_CONV (K th))) THEN
  SRW_TAC [][EXP_ADD, DECIDE ``x * 2 = x + x``, MOD_LESS])

val LOG2_UNIQUE_BOUNDS = store_thm(
  "LOG2_UNIQUE_BOUNDS",
  `!m n. 2 ** n <= m /\ m < 2 ** (n + 1) ==> (LOG2 m = n)`,
  REPEAT STRIP_TAC THEN
  SPOSE_NOT_THEN ASSUME_TAC THEN
  `0 < m` by PROVE_TAC [LESS_LESS_EQ_TRANS, ZERO_LT_TWOEXP] THEN
  `LOG2 m < n \/ n < LOG2 m` by DECIDE_TAC THENL [
     `LOG2 m + 1 <= n` by DECIDE_TAC THEN
     `2 ** (LOG2 m + 1) <= 2 ** n` by SRW_TAC [][] THEN
     `m < 2 ** (LOG2 m + 1)` by SRW_TAC [][LOG2_UBOUND] THEN
     DECIDE_TAC,
     `n + 1 <= LOG2 m` by DECIDE_TAC THEN
     `2 ** (n + 1) <= 2 ** LOG2 m` by SRW_TAC [][] THEN
     `2 ** LOG2 m <= m` by SRW_TAC [][LOG2_LBOUND] THEN
     DECIDE_TAC
  ])

val LOG2_2EXPN =
  (GEN_ALL o
    SIMP_RULE arith_ss [ZERO_LT_TWOEXP,DECIDE ``!a b. 0 < b ==> 0 < a + b``] o
   SPEC `2 ** n + r`) LOG2;

val LOG2_2EXPN_0 =
  (GEN_ALL o SIMP_RULE arith_ss [ZERO_LT_TWOEXP] o SPEC `2 ** n`) LOG2;

val lem = prove(
  `!a b. a < b ==> (2 ** b MOD 2 ** a = 0)`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_ADD
    THEN POP_ASSUM (SUBST1_TAC o SYM)
    THEN ASM_SIMP_TAC arith_ss [EXP_ADD,MOD_EQ_0,ZERO_LT_TWOEXP]
);

val LOG2_POWER = prove(
  `!q. q = LOG2 (2 ** q)`,
  GEN_TAC THEN
  Q_TAC SUFF_TAC `2 ** q <= 2 ** q /\ 2 ** q < 2 ** (q + 1)` THEN1
        METIS_TAC [LOG2_UNIQUE_BOUNDS] THEN
  SRW_TAC [][])

val lem2 = DECIDE ``!a b c. a < c /\ b < c ==> a + b < d + (c * 2 + 1)``;

val lem3 = prove(
  `!a b c d. a < b /\ c < 2 ** (b - 1) ==> 2 ** a + c < 2 ** b + (SUC d)`,
  Induct_on `b` THEN RW_TAC arith_ss []
    THEN Cases_on `a = b` THEN FULL_SIMP_TAC arith_ss [ADD1,EXP_ADD]
    THEN `a < b` by DECIDE_TAC
    THEN Cases_on `2 ** (b - 1) <= c` THEN FULL_SIMP_TAC arith_ss [ADD1,EXP_ADD]
    THENL [
      MATCH_MP_TAC lem2 THEN METIS_TAC [TWOEXP_MONO],
      FULL_SIMP_TAC arith_ss [NOT_LESS_EQUAL]
        THEN RES_TAC THEN POP_ASSUM (ASSUME_TAC o SPEC `d`)
        THEN DECIDE_TAC
    ]
);

val lem4 = prove(
  `!q n. SUC n < 2 ** q ==> ~(LOG2 (SUC n + 2 ** q) = q - 1)`,
  REPEAT STRIP_TAC
    THEN ASSUME_TAC (SPECL [`SUC n`,`q`] LOG2_2EXPN)
    THEN PAT_ASSUM `LOG2 (SUC n + 2 ** q) = q - 1` SUBST_ALL_TAC
    THEN Cases_on `q` THEN FULL_SIMP_TAC arith_ss []
    THEN `(SUC n + 2 ** SUC n') MOD 2 ** n' < 2 ** n'`
      by ASM_SIMP_TAC arith_ss [MOD_2EXP_LT]
    THEN NTAC 2 (POP_ASSUM MP_TAC) 
    THEN Q.SPEC_TAC (`(SUC n + 2 ** SUC n') MOD 2 ** n'`, `k`)
    THEN RW_TAC arith_ss [EXP]
);

val LOG2_UNIQUE = store_thm("LOG2_UNIQUE",
  `!n q. (?r. (n = 2 ** q + r) /\ r < 2 ** q) ==> (LOG2 n = q)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LOG2_UNIQUE_BOUNDS THEN
  SRW_TAC [ARITH_ss][EXP_ADD])

(* -------------------------------------------------------- *)

val BITWISE_compute = prove(
  `!n opr a b.
      BITWISE n opr a b =
        if n = 0 then 0 else
          2 * BITWISE (PRE n) opr (DIV2 a) (DIV2 b) +
          (if opr (ODD a) (ODD b) then 1 else 0)`,
  Cases THEN1 REWRITE_TAC [CONJUNCT1 BITWISE_def]
    THEN REWRITE_TAC [DIV2_def, numTheory.NOT_SUC,
                      PRE, EXP, BITWISE_EVAL, LSB_ODD, SBIT_def]);

val _ =
 let open EmitML
 in
   emitML (!Globals.emitMLDir)
  ("bits",
    MLSIG "type num = numML.num" 
     :: 
    OPEN ["num"]
     ::
    map (DEFN o PURE_REWRITE_RULE [arithmeticTheory.NUMERAL_DEF])
        [TIMES_2EXP_def, DIV_2EXP_def, MOD_2EXP_def,
         DIVMOD_2EXP, SBIT_def, BITS_def,
         BITV_def, BIT_def, SLICE_def,LSBn_def,
         SIGN_EXTEND_def, BITWISE_compute])
 end;

val _ = export_theory();
val _ = export_doc_theorems();

(* -------------------------------------------------------- *)
