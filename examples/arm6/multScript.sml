(* app load ["pred_setSimps","bitsTheory","armTheory","coreTheory","lemmasTheory",
             "interruptsTheory","compLib","word32Lib"]; *)
open HolKernel boolLib bossLib Q arithmeticTheory whileTheory
     bitsTheory word32Theory armTheory coreTheory
     lemmasTheory compLib interruptsTheory;

(* -------------------------------------------------------- *)

val _ = new_theory "mult";

val _ = numLib.prefer_num();

val std_ss = std_ss ++ boolSimps.LET_ss;
val arith_ss = arith_ss ++ boolSimps.LET_ss;

(* -------------------------------------------------------- *)

val MULT_ALU6_ZERO = store_thm("MULT_ALU6_ZERO",
  `!ireg borrow2 mul dataabt alua alub c.
     SND (ALU6 mla_mul t3 ireg borrow2 mul dataabt alua alub c) =
       if WORD_BIT 21 ireg then
          alub
       else
          0w`,
  RW_TAC std_ss [ALUOUT_ALU_logic,ALU6_def]
);

(* -------------------------------------------------------- *)

val COMM_MULT_DIV = ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV;
val COMM_DIV_MULT = ONCE_REWRITE_RULE [MULT_COMM] DIV_MULT;

(* -------------------------------------------------------- *)

val WL = SIMP_RULE arith_ss [HB_def] WL_def;

(* -------------------------------------------------------- *)

val WORD_BITS_HB_0 =
  SIMP_CONV bool_ss [WORD_BITS_def,SYM MOD_WL_THM,GSYM w2n_EVAL,w2n_ELIM] ``WORD_BITS HB 0 rs``;

val COMP_VAL_BIT2 = prove(
  `!a b c d. (~(\(w,a). w /\ (a = 15)) if (c = 15) \/ (c = d) then (F,b) else (T,c))`,
  RW_TAC std_ss [] THEN FULL_SIMP_TAC bool_ss []
);

val MIN_LEM = prove(
  `!x t. 0 < t ==> (MIN x (x - 2 + 2 * t) = x)`,
  RW_TAC arith_ss [MIN_DEF]
);

val BORROW2 = prove(
  `!n rs. BORROW2 rs n = ~(n = 0) /\ BIT 1 (WORD_BITS (2 * (n - 1) + 1) (2 * (n - 1)) rs)`,
  Cases THEN SIMP_TAC arith_ss [BORROW2_def]
    THEN SIMP_TAC arith_ss [BIT_def,WORD_BITS_COMP_THM2,GSYM WORD_BIT_THM,ADD1,LEFT_ADD_DISTRIB]
);

val MULX_DONE_def = prove(
  `!n rs.
     2 * (SUC n) <= WL ==>
      (MULX mla_mul tn (MULZ mla_mul tn (WORD_BITS HB (2 * SUC n) rs)) (BORROW2 rs (SUC n))
          (MSHIFT mla_mul (BORROW2 rs n) (BITS 1 0 (WORD_BITS HB (2 * n) rs)) n) =
       MLA_MUL_DONE rs (SUC n))`,
  RW_TAC arith_ss [MULX_def,MULZ_def,MSHIFT,MLA_MUL_DONE_def,MIN_LEM,
                   MULT_DIV,DIV_MULT,WORD_BITS_COMP_THM2,WL]
    THEN FULL_SIMP_TAC arith_ss [DECIDE ``!a b c. (a \/ b = a \/ c) = (~a ==> (b = c))``]
);

val MULX_DONE_ZERO =
  (SIMP_RULE arith_ss [SIMP_CONV arith_ss [HB_def] ``MIN HB 1``,WL,
                       MSHIFT,BORROW2,WORD_BITS_COMP_THM2] o SPEC `0`) MULX_DONE_def;

(* -------------------------------------------------------- *)

val WL_EVEN = prove(
  `WL MOD 2 = 0`,
  SIMP_TAC arith_ss [WL]
);

val EXISTS_DONE = prove(
  `!rs. ?n. MLA_MUL_DONE rs n`,
  RW_TAC bool_ss [MLA_MUL_DONE_def]
    THEN EXISTS_TAC `WL DIV 2`
    THEN SIMP_TAC arith_ss [DIV_MULT_THM2,WL_EVEN]
);

val lem = (SIMP_RULE bool_ss [EXISTS_DONE] o
           SPECL [`\x. 2 * x <= WL`,`MLA_MUL_DONE rs`]) LEAST_ELIM;

val SPEC_LESS_MULT_MONO =
  (GEN_ALL o numLib.REDUCE_RULE o INST [`n` |-> `1`] o SPEC_ALL) LESS_MULT_MONO;

val DIV_TWO_MONO_EVEN = prove(
  `!a b. a < 2 * b = a DIV 2 < b`,
  REPEAT STRIP_TAC
    THEN Cases_on `EVEN a`
    THENL [
      IMP_RES_TAC EVEN_EXISTS
        THEN ASM_SIMP_TAC arith_ss [COMM_MULT_DIV,SPEC_LESS_MULT_MONO],
      RULE_ASSUM_TAC (REWRITE_RULE [GSYM ODD_EVEN])
        THEN IMP_RES_TAC ODD_EXISTS
        THEN ASM_SIMP_TAC arith_ss [ADD1,COMM_DIV_MULT,SPEC_LESS_MULT_MONO]
    ]
);

val WL_DIV_MULT_TWO_ID = (SYM o ONCE_REWRITE_RULE [MULT_COMM] o SIMP_RULE arith_ss [WL_EVEN] o
                          CONJUNCT1 o SPEC `WL` o numLib.REDUCE_RULE o SPEC `2`) DIVISION;

val DONE_LESS_EQUAL_WL = prove(
  `!n. (!m. m < n ==> ~MLA_MUL_DONE rs m) /\ MLA_MUL_DONE rs n ==> 2 * n <= WL`,
  RW_TAC bool_ss [MLA_MUL_DONE_def,NOT_LESS]
    THENL [
       FULL_SIMP_TAC arith_ss [BORROW2_def]
         THEN SPOSE_NOT_THEN STRIP_ASSUME_TAC
         THEN RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS_EQUAL])
         THEN IMP_RES_TAC DIV_TWO_MONO_EVEN
         THEN PAT_ASSUM `!m. m < n ==> P` IMP_RES_TAC
         THEN FULL_SIMP_TAC arith_ss [WL_DIV_MULT_TWO_ID],
       Cases_on `2 * n = WL` THEN1 ASM_SIMP_TAC arith_ss []
         THEN `WL < 2 * n` by DECIDE_TAC
         THEN IMP_RES_TAC DIV_TWO_MONO_EVEN
         THEN PAT_ASSUM `!m. m < n ==> P` IMP_RES_TAC
         THEN FULL_SIMP_TAC arith_ss [WL_DIV_MULT_TWO_ID]
    ]
);

val DUR_LT_EQ_HWL = prove(
  `!rs. 2 * (MLA_MUL_DUR rs) <= WL`,
  REWRITE_TAC [MLA_MUL_DUR_def]
    THEN CONV_TAC (DEPTH_CONV ETA_CONV)
    THEN PROVE_TAC [DONE_LESS_EQUAL_WL,lem]
);

(* -------------------------------------------------------- *)

val lem = (SIMP_RULE arith_ss [EXISTS_DONE,MLA_MUL_DONE_def,WL_def] o
           SPECL [`\x. ~(x = 0)`,`MLA_MUL_DONE rs`]) LEAST_ELIM;

val DUR_NEQ_ZERO = prove(
  `!rs. ~(MLA_MUL_DUR rs = 0)`,
  REWRITE_TAC [MLA_MUL_DUR_def]
    THEN CONV_TAC (DEPTH_CONV ETA_CONV)
    THEN PROVE_TAC [lem]
);

(* -------------------------------------------------------- *)

val DONE_DUR = prove(
  `!rs. MLA_MUL_DONE rs (MLA_MUL_DUR rs)`,
  REWRITE_TAC [MLA_MUL_DUR_def]
    THEN CONV_TAC (DEPTH_CONV ETA_CONV)
    THEN PROVE_TAC [LEAST_EXISTS_IMP,EXISTS_DONE]
);

val NOT_DONE_SUC = prove(
  `!rs n. SUC n <= MLA_MUL_DUR rs ==> ~MLA_MUL_DONE rs n`,
  RW_TAC bool_ss [MLA_MUL_DUR_def]
    THEN RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV))
    THEN ASM_SIMP_TAC arith_ss [LESS_LEAST]
);

(* -------------------------------------------------------- *)

val BITS_X_SUB2 = prove(
  `!n x rs. ~(n = 0) ==> (BITS (x - 2) 0 (WORD_BITS x (2 * n) rs) = WORD_BITS x (2 * n) rs)`,
  SIMP_TAC arith_ss [WORD_BITS_COMP_THM2,MIN_LEM]
);

val SPEC_MULT_LESS_EQ_SUC =
  (GEN_ALL o REWRITE_RULE [SYM TWO] o INST [`p` |-> `1`] o SPEC_ALL) MULT_LESS_EQ_SUC;

val LEQ_MLA_MUL_DUR = prove(
  `!n rs. n <= MLA_MUL_DUR rs ==> 2 * n <= WL`,
  REPEAT STRIP_TAC
    THEN RULE_ASSUM_TAC (ONCE_REWRITE_RULE [SPEC_MULT_LESS_EQ_SUC])
    THEN PROVE_TAC [LESS_EQ_TRANS,DUR_LT_EQ_HWL]
);

val MUL1 = prove(
  `!rs n. SUC n <= MLA_MUL_DUR rs ==>
            (BITS 1 0 (WORD_BITS HB (2 * n) rs) = WORD_BITS (2 * n + 1) (2 * n) rs)`,
  RW_TAC arith_ss [ADD1,WORD_BITS_COMP_THM2,MIN_DEF]
    THEN IMP_RES_TAC LEQ_MLA_MUL_DUR
    THEN FULL_SIMP_TAC arith_ss [WL_def]
);

val MUL1_SUC = prove(
  `!n x. BITS x 2 (WORD_BITS x (2 * (n + 1)) rs) =
         WORD_BITS x (2 * (n + 2)) rs`,
  SIMP_TAC arith_ss [WORD_BITS_COMP_THM2,MIN_DEF,LEFT_ADD_DISTRIB]
);

val COUNT1 = prove(
  `!n b. (n * 2 + (if b then 1 else 0)) DIV 2 = n`,
  RW_TAC arith_ss [MULT_DIV,DIV_MULT]
);

val BITS_X_SUB2_1 = (SIMP_RULE arith_ss [] o SPEC `1`) BITS_X_SUB2;
val MUL1_SUC_1 = (SIMP_RULE arith_ss [] o SPEC `0`) MUL1_SUC;
val COUNT1_ZERO = (SIMP_RULE arith_ss [] o SPEC `0`) COUNT1;

val MOD_4_BITS = prove(
  `!a. a MOD 4 = BITS 1 0 a`,
  SIMP_TAC arith_ss [BITS_ZERO3]
);

val SPEC_MULX_DONE =
  (GEN_ALL o SIMP_RULE bool_ss [] o DISCH `~(n = 0)` o
   CONV_RULE (RAND_CONV (REWRITE_CONV [ADD1])) o
   SIMP_RULE arith_ss [MUL1,MSHIFT,BORROW2,AND_IMP_INTRO,
     MATCH_MP (DECIDE ``!a b. (a ==> b) ==> (a /\ b = a)``)
              (SPECL [`SUC n`,`rs`] LEQ_MLA_MUL_DUR)] o
   DISCH `SUC n <= MLA_MUL_DUR rs` o SPEC_ALL) MULX_DONE_def;

val COUNT1_ID = prove(
  `!rs n. SUC n <= MLA_MUL_DUR rs ==> (BITS 3 0 n = n)`,
  REPEAT STRIP_TAC
    THEN POP_ASSUM (fn th => ASSUME_TAC (MATCH_MP LEQ_MLA_MUL_DUR th))
    THEN IMP_RES_TAC ((SIMP_RULE arith_ss [] o SPEC `2`) DIV_LE_MONOTONE)
    THEN FULL_SIMP_TAC arith_ss [COMM_MULT_DIV,WL,BITS_ZEROL]
);

(* -------------------------------------------------------- *)

val DONE_NEQ_ZERO = prove(
  `!rs. ~MLA_MUL_DONE rs 0`,
  SIMP_TAC arith_ss [MLA_MUL_DONE_def,WL_def]
);

(* -------------------------------------------------------- *)

val DIV_2_BITS = (GEN_ALL o SYM o numLib.REDUCE_RULE o INST [`n` |-> `1`] o SPEC_ALL) WORD_BITS_DIV_THM;

val BIT_CONST = prove(
  `~(BIT 1 0) /\ ~(BIT 1 1) /\ (BIT 1 2) /\ (BIT 1 3)`,
  EVAL_TAC
);

val BIT_VAR = prove(
  `!t x. ~(WORD_BITS (t + 1) t x = 0) /\ ~(WORD_BITS (t + 1) t x = 1) ==>
          BIT 1 (WORD_BITS (t + 1) t x)`,
  RW_TAC arith_ss [BIT_def,WORD_BITS_COMP_THM2,MIN_DEF,DIV_2_BITS]
    THEN Cases_on `WORD_BITS (t + 1) t x = 2`
    THEN1 ASM_SIMP_TAC arith_ss []
    THEN Cases_on `WORD_BITS (t + 1) t x = 3`
    THEN1 ASM_SIMP_TAC arith_ss []
    THEN ASSUME_TAC ((SIMP_RULE arith_ss [ADD1] o SPECL [`t + 1`,`t`,`x`]) WORD_BITSLT_THM)
    THEN DECIDE_TAC
);

val BIT_VAR0 = (SIMP_RULE arith_ss [] o SPEC `0`) BIT_VAR;

(* -------------------------------------------------------- *)

val CARRY_LEM = store_thm("CARRY_LEM",
  `!cpsr. NZCV (w2n cpsr) = FST (DECODE_PSR cpsr)`,
  SIMP_TAC std_ss [DECODE_PSR]
);

val LSL_CARRY_SUBST = prove(
  `!n C x c. ~(n = 0) ==> (LSL x n c = LSL x n C)`,
  SIMP_TAC std_ss [LSL_def]
);

(* -------------------------------------------------------- *)

val lem = (SIMP_RULE bool_ss [EXISTS_DONE] o
           SPECL [`\x. 2 * x < WL ==> ~(BORROW2 rs x)`,`MLA_MUL_DONE rs`]) LEAST_ELIM;

val DONE_EARLY_NOT_BORROW = prove(
  `!n. (!m. m < n ==> ~MLA_MUL_DONE rs m) /\ MLA_MUL_DONE rs n ==>
          2 * n < WL ==>
          ~BORROW2 rs n`,
  RW_TAC arith_ss [MLA_MUL_DONE_def,BORROW2_def]
    THEN FULL_SIMP_TAC bool_ss []
);

val DONE_EARLY_NOT_BORROW2 = prove(
  `!rs. 2 * (MLA_MUL_DUR rs) < WL ==> ~BORROW2 rs (MLA_MUL_DUR rs)`,
  REWRITE_TAC [MLA_MUL_DUR_def]
    THEN CONV_TAC (DEPTH_CONV ETA_CONV)
    THEN PROVE_TAC [MATCH_MP lem DONE_EARLY_NOT_BORROW]
);

val BORROW_IMP_WL = prove(
  `!rs. BORROW2 rs (MLA_MUL_DUR rs) ==> (2 * (MLA_MUL_DUR rs) = WL)`,
  REPEAT STRIP_TAC
    THEN Cases_on `2 * (MLA_MUL_DUR rs) < WL`
    THEN1 IMP_RES_TAC DONE_EARLY_NOT_BORROW2
    THEN ASSUME_TAC (SPEC `rs` DUR_LT_EQ_HWL)
    THEN DECIDE_TAC
);

val lem = (SIMP_RULE bool_ss [EXISTS_DONE] o
           SPECL [`\x. w2n rs MOD 2 ** (2 * x) = w2n rs`,`MLA_MUL_DONE rs`]) LEAST_ELIM;

val ZERO_LT_WL = simpLib.SIMP_PROVE arith_ss [WL_def] ``0 < WL``;

val DONE_IMP_ZERO_MSBS = prove(
  `!n. (!m. m < n ==> ~MLA_MUL_DONE rs m) /\ MLA_MUL_DONE rs n ==>
        (w2n rs MOD 2 ** (2 * n) = w2n rs)`,
   STRUCT_CASES_TAC (SPEC `rs` word_nchotomy)
     THEN RW_TAC arith_ss [WL_def,SUC_SUB1,w2n_EVAL,MLA_MUL_DONE_def,MOD_WL_THM,WORD_BITS_def,BITS_COMP_THM2]
     THENL [
       Cases_on `n'` THEN1 FULL_SIMP_TAC arith_ss [ZERO_MOD]
         THEN FULL_SIMP_TAC bool_ss [GSYM BITS_ZERO3,DECIDE ``!n. 2 * SUC n = SUC (2 * n + 1)``]
         THEN RW_TAC arith_ss [BITS_COMP_THM2,MIN_DEF]
         THEN Cases_on `2 * n'' + 1 = HB` THEN1 ASM_REWRITE_TAC []
         THEN `2 * n'' + 2 <= HB` by FULL_SIMP_TAC arith_ss [NOT_LESS]
         THEN `SLICE HB (SUC (2 * n'' + 1)) n = 0` by ASM_SIMP_TAC arith_ss [SLICE_THM]
         THEN IMP_RES_TAC ((GSYM o SIMP_RULE arith_ss [ADD1,SLICE_ZERO_THM] o
                                      SPECL [`HB`,`2 * n'' + 1`,`0`]) SLICE_COMP_THM)
         THEN POP_ASSUM (ASSUME_TAC o SPEC `n`)
         THEN FULL_SIMP_TAC arith_ss [ADD1],
       FULL_SIMP_TAC bool_ss [NOT_LESS]
         THEN IMP_RES_TAC LESS_EQUAL_ADD
         THEN STRIP_ASSUME_TAC (REWRITE_RULE [ADD,WL_def] (MATCH_MP LESS_ADD_1 ZERO_LT_WL))
         THEN ASM_SIMP_TAC bool_ss [ADD_SUB,DECIDE ``!a b. a + 1 + b = SUC (a + b)``,GSYM BITS_ZERO3]
         THEN RW_TAC arith_ss [BITS_COMP_THM2,MIN_DEF]
         THEN `p = 0` by DECIDE_TAC
         THEN FULL_SIMP_TAC arith_ss [ADD1]
     ]
);

val DUR_IMP_ZERO_MSBS = prove(
  `!rs. w2n rs MOD 2 ** (2 * (MLA_MUL_DUR rs)) = w2n rs`,
  REWRITE_TAC [MLA_MUL_DUR_def]
    THEN CONV_TAC (DEPTH_CONV ETA_CONV)
    THEN PROVE_TAC [MATCH_MP lem DONE_IMP_ZERO_MSBS]
);

val SPEC_LSL_LIMIT = (GEN_ALL o REWRITE_RULE [GSYM WL_def] o
                      SIMP_RULE arith_ss [WL_def] o SPECL [`a`,`WL`]) LSL_LIMIT;

val RD_INVARIANT_def = Define`
  RD_INVARIANT A rm rs rn n =
    (if BORROW2 rs n then
       rm * n2w (w2n rs MOD 2 ** (2 * n)) - rm << (2 * n)
     else
       rm * n2w (w2n rs MOD 2 ** (2 * n))) +
    (if A then rn else 0w)`;

val BORROW2_LEM1 = prove(
  `!a. WORD_BIT 1 rs = BIT 1 (WORD_BITS 1 0 rs)`,
  SIMP_TAC arith_ss [BIT_def,WORD_BITS_COMP_THM2,WORD_BIT_THM]
);

val RD_INVARIANT_ZERO =
  (GEN_ALL o SIMP_RULE arith_ss [BORROW2_def,WORD_MULT_CLAUSES,WORD_ADD_CLAUSES] o
   INST [`n` |-> `0`] o SPEC_ALL) RD_INVARIANT_def;

val RD_INVARIANT_ONE =
  (GEN_ALL o SIMP_RULE arith_ss [BORROW2_def,MOD_4_BITS,GSYM WORD_BITS_def,BORROW2_LEM1] o
   INST [`n` |-> `1`] o SPEC_ALL) RD_INVARIANT_def;

val RD_INVARIANT_LAST = store_thm("RD_INVARIANT_LAST",
  `!a rm rs rn.
     RD_INVARIANT a rm rs rn (MLA_MUL_DUR rs) =
       rm * rs + (if a then rn else 0w)`,
   RW_TAC bool_ss [RD_INVARIANT_def,BORROW_IMP_WL,DUR_IMP_ZERO_MSBS,SPEC_LSL_LIMIT,
                   w2n_ELIM,WORD_ADD_0,WORD_SUB_RZERO]
);

(* -------------------------------------------------------- *)

val MUST_BE_TWO = prove(
  `!t x. ~(WORD_BITS (t + 1) t x = 0) /\
         ~(WORD_BITS (t + 1) t x = 1) /\
         ~(WORD_BITS (t + 1) t x = 3) ==>
          (WORD_BITS (t + 1) t x = 2)`,
  REPEAT STRIP_TAC
    THEN Cases_on `WORD_BITS (t + 1) t x = 2`
    THEN1 ASM_REWRITE_TAC []
    THEN ASSUME_TAC ((SIMP_RULE arith_ss [ADD1] o SPECL [`t + 1`,`t`,`x`]) WORD_BITSLT_THM)
    THEN DECIDE_TAC
);

val MUST_BE_THREE = prove(
  `!t x. ~(WORD_BITS (t + 1) t x = 0) /\
         ~(WORD_BITS (t + 1) t x = 1) /\
         ~(WORD_BITS (t + 1) t x = 2) ==>
          (WORD_BITS (t + 1) t x = 3)`,
  REPEAT STRIP_TAC
    THEN Cases_on `WORD_BITS (t + 1) t x = 3` THEN1 ASM_REWRITE_TAC []
    THEN ASSUME_TAC ((SIMP_RULE arith_ss [ADD1] o SPECL [`t + 1`,`t`,`x`]) WORD_BITSLT_THM)
    THEN DECIDE_TAC
);

val MUST_BE_THREE_0 = (SIMP_RULE arith_ss [] o SPEC `0`) MUST_BE_THREE;

(* -------------------------------------------------------- *)

val SPEC_SLICE_COMP = prove(
  `!t a. ~(t = 0) ==>
         (a MOD 2 ** (2 * (t + 1)) =
          SLICE (2 * t + 1) (2 * t) a + a MOD 2 ** (2 * t))`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC NOT_ZERO_ADD1
    THEN ASM_SIMP_TAC arith_ss [DECIDE (Term `!p. 2 * SUC p = SUC (2 * p + 1)`),
                               GSYM BITS_ZERO3,GSYM SLICE_ZERO_THM,SLICE_COMP_RWT]
    THEN SIMP_TAC arith_ss [SLICE_ZERO_THM,BITS_ZERO3,ADD1,LEFT_ADD_DISTRIB]
);

val MULT_MOD_SUC_T = prove(
  `!t a b.  a * n2w (w2n b MOD 2 ** (2 * (t + 1))) =
            (a * n2w (w2n b MOD 2 ** (2 * t))) + (a * n2w (WORD_SLICE (2 * t + 1) (2 * t) b))`,  REPEAT STRIP_TAC
    THEN Cases_on `t = 0`
    THEN1 ASM_SIMP_TAC arith_ss [WORD_MULT_CLAUSES,WORD_ADD_CLAUSES,
                                 MOD_4_BITS,GSYM WORD_BITS_def,WORD_SLICE_ZERO_THM]
    THEN ASM_SIMP_TAC bool_ss [SPEC_SLICE_COMP,GSYM WORD_SLICE_def,GSYM ADD_EVAL,
                               WORD_LEFT_ADD_DISTRIB,WORD_ADD_COMM]
);

val MULT_LEM = prove(
  `!a b c. a * n2w (b * c) = (a * n2w c) * n2w b`,
  SIMP_TAC bool_ss [GSYM MUL_EVAL,AC WORD_MULT_ASSOC WORD_MULT_COMM]
);

val MULT_MOD_SUC_T = save_thm("MULT_MOD_SUC_T",REWRITE_RULE [MULT_LEM,WORD_SLICE_THM,GSYM word_lsl] MULT_MOD_SUC_T);

(* -------------------------------------------------------- *)

val MULT_TWO = prove(
  `!a. a * n2w 2 = a + a`,
  STRIP_TAC THEN STRUCT_CASES_TAC (SPEC `a` word_nchotomy)
    THEN SIMP_TAC arith_ss [MULT_COMM,ADD_EVAL,MUL_EVAL]
);

val MULT_THEE = prove(
  `!a. a * n2w 3 = a * n2w 2 + a`,
  REWRITE_TAC [MULT_TWO]
    THEN STRIP_TAC THEN STRUCT_CASES_TAC (SPEC `a` word_nchotomy)
    THEN SIMP_TAC arith_ss [ADD_EVAL,MUL_EVAL]
    THEN SIMP_TAC (bool_ss++numSimps.ARITH_AC_ss) []
);

val MULT_FOUR = prove(
  `!a. a * n2w 4 = (a * n2w 2) + (a * n2w 2)`,
  STRIP_TAC THEN STRUCT_CASES_TAC (SPEC `a` word_nchotomy)
    THEN SIMP_TAC arith_ss [AC MULT_ASSOC MULT_COMM,ADD_EVAL,MUL_EVAL]
);

val MULT_TWO_LSL = prove(
  `!rm t. rm << (t * 2 + 1) = (rm << (2 * t)) * n2w 2`,
  SIMP_TAC arith_ss [word_lsl,GSYM WORD_MULT_ASSOC,MUL_EVAL,GSYM ADD1,EXP,MULT_COMM]
);

val MULT_FOUR_LSL = prove(
  `!t rm. rm << (2 * (t + 1)) = (rm << (2 * t)) * n2w 4`,
  SIMP_TAC arith_ss [word_lsl,GSYM WORD_MULT_ASSOC,MUL_EVAL,LEFT_ADD_DISTRIB,EXP_ADD]
);

val SPEC_WORD_EQ_ADD_RCANCEL =
  (GEN_ALL o REWRITE_RULE [WORD_ADD_ASSOC] o
   CONV_RULE (LAND_CONV (LAND_CONV (RAND_CONV (ONCE_REWRITE_CONV [WORD_ADD_COMM])))) o
   REWRITE_RULE [GSYM WORD_ADD_ASSOC] o
   SPECL [`a + b`,`c`,`p`]) WORD_EQ_ADD_RCANCEL;

val ALU6_MUL_def = Define`
  ALU6_MUL borrow2 mul (alua:word32) alub =
    if ~borrow2 /\ (mul = 0) \/ borrow2 /\ (mul = 3) then
      alua
    else if borrow2 /\ (mul = 0) \/ (mul = 1) then
      alua + alub
    else
      alua - alub`;

val BORROW_LEM2 = prove(
  `!rs n. ((WORD_BITS (2 * n + 1) (2 * n) rs = 0) \/
           (WORD_BITS (2 * n + 1) (2 * n) rs = 1) ==> ~BORROW2 rs (n + 1)) /\
          ((WORD_BITS (2 * n + 1) (2 * n) rs = 2) \/
           (WORD_BITS (2 * n + 1) (2 * n) rs = 3) ==> BORROW2 rs (n + 1))`,
   RW_TAC arith_ss [BORROW2] THEN ASM_SIMP_TAC std_ss [BIT_CONST]
);

val RD_INVARIANT_THM = store_thm("RD_INVARIANT_THM",
  `!n a rm rs rn. 
      RD_INVARIANT a rm rs rn (n + 1) =
        let borrow2 = BORROW2 rs n
        and mul = WORD_BITS (2 * n + 1) (2 * n) rs
        in
          ALU6_MUL borrow2 mul (RD_INVARIANT a rm rs rn n) (rm << MSHIFT2 borrow2 mul n)`,
  RW_TAC std_ss [BORROW_LEM2,MSHIFT2_def,RD_INVARIANT_def,ALU6_MUL_def]
    THEN FULL_SIMP_TAC arith_ss [BORROW_LEM2]
    THEN FULL_SIMP_TAC bool_ss [BORROW_LEM2,MUST_BE_TWO,MUST_BE_THREE,MULT_MOD_SUC_T,
            WORD_MULT_CLAUSES,WORD_ADD_CLAUSES,AC MULT_ASSOC MULT_COMM,
            WORD_ADD_ASSOC,WORD_SUB_PLUS,WORD_ADD_SUB_SYM,WORD_SUB_ADD,
            WORD_EQ_ADD_RCANCEL,SPEC_WORD_EQ_ADD_RCANCEL,
            MULT_FOUR_LSL,MULT_TWO_LSL,MULT_TWO,MULT_THEE,MULT_FOUR]
    THEN ASM_SIMP_TAC bool_ss [GSYM WORD_ADD_SUB_SYM,WORD_ADD_SUB]
);

val RD_INVARIANT_SUC = prove(
  `!n a rs.
      ~(n = 0) /\
      (BIT 1 (WORD_BITS (2 * (n - 1) + 1) (2 * (n - 1)) rs) = borrow2) /\
      (WORD_BITS (2 * n + 1) (2 * n) rs = mul) ==>
      ((if ~borrow2 /\ (mul = 0) \/ borrow2 /\ (mul = 3) then
          RD_INVARIANT a rm rs rn n
        else
          (if borrow2 /\ (mul = 0) \/ (mul = 1) then
             RD_INVARIANT a rm rs rn n +
             rm << (n * 2 + (if borrow2 /\ (mul = 1) \/ ~borrow2 /\ (mul = 2) then 1 else 0))
           else
             RD_INVARIANT a rm rs rn n -
             rm << (n * 2 + (if ~borrow2 /\ (mul = 2) then 1 else 0)))) =
        RD_INVARIANT a rm rs rn (n + 1))`,
  RW_TAC std_ss [RD_INVARIANT_THM,ALU6_MUL_def,BORROW2,MSHIFT2_def]
);

val RD_ONE = (GSYM o
  SIMP_RULE arith_ss [RD_INVARIANT_def,BORROW2,MOD_4_BITS,GSYM WORD_BITS_def] o
  SIMP_RULE arith_ss [RD_INVARIANT_ZERO,BORROW2_def,MSHIFT2_def,
                      ALU6_MUL_def,ZERO_SHIFT2] o SPEC `0`) RD_INVARIANT_THM;

(* -------------------------------------------------------- *)

val SET_NZC_IDEM = prove(
  `!a b xpsr. SET_NZC a (SET_NZC b xpsr) = SET_NZC a xpsr`,
  Cases THEN Cases THEN Cases_on `r` THEN Cases_on `r'`
    THEN SIMP_TAC bool_ss [SET_NZC_def,SET_NZCV_IDEM,WORD_BIT_def,DECODE_NZCV_SET_NZCV]
);

val DECODE_MODE_SET_NZC = prove(
  `!nzc psr. DECODE_MODE (WORD_BITS 4 0 (SET_NZC nzc psr)) =
             DECODE_MODE (WORD_BITS 4 0 psr)`,
  Cases THEN Cases_on `r`
    THEN SIMP_TAC bool_ss [SET_NZC_def,WORD_BITS_def,DECODE_MODE_def,DECODE_IFMODE_SET_NZCV]
);

val IF_FLAGS_SET_NZC = prove(
  `!nzc psr n. (n = 6) \/ (n = 7) ==> (WORD_BIT n (SET_NZC nzc psr) = WORD_BIT n psr)`,
  Cases THEN Cases_on `r`
    THEN RW_TAC bool_ss [SET_NZC_def,WORD_BIT_def]
    THEN SIMP_TAC bool_ss [DECODE_IFMODE_SET_NZCV]
);

val IF_FLAGS_SET_NZC_COND = prove(
  `!nzc psr b n. (n = 6) \/ (n = 7) ==>
     (BIT n (w2n (if b then SET_NZC nzc psr else psr)) = BIT n (w2n psr))`,
  RW_TAC bool_ss [GSYM WORD_BIT_def] THEN SIMP_TAC bool_ss [IF_FLAGS_SET_NZC]
);

(* -------------------------------------------------------- *)

val REG_WRITE_READ_NEQ_15 =
   (SIMP_RULE arith_ss [TO_WRITE_READ6] o INST [`n2` |-> `15`] o SPEC_ALL) REG_WRITE_READ_NEQ;

(* -------------------------------------------------------- *)

val MLA_MUL_INVARIANT = Count.apply prove(
  `!n x i mem reg psr alua pipeb ireg ointstart obaselatch onfq ooonfq oniq oooniq
    pipeaabt pipebabt dataabt2 aregn2 sctrl psrfb orp.
    (Abbrev (pc = REG_READ6 reg usr 15)) /\
    (Abbrev (cpsr = CPSR_READ psr)) /\
    (Abbrev (nbs = DECODE_MODE (WORD_BITS 4 0 cpsr))) /\
    (!t. t < 1 + MLA_MUL_DUR (REG_READ6 reg nbs (WORD_BITS 11 8 ireg)) ==> FST (i t)) /\
    n <= MLA_MUL_DUR (REG_READ6 reg nbs (WORD_BITS 11 8 ireg)) ==>
    ?ointstart' obaselatch' onfq' ooonfq' oniq' oooniq' pipeaabt' pipebabt' iregabt' dataabt' aregn'.
      ~(num2exception aregn' IN {reset; undefined; software; address}) /\ (aregn' < 8) /\
      let Rm = WORD_BITS 3 0 ireg
      and Rd = WORD_BITS 19 16 ireg
      and rs = REG_READ6 reg nbs (WORD_BITS 11 8 ireg)
      and rn = REG_READ6 reg nbs (WORD_BITS 15 12 ireg)
      in
      let rm = REG_READ6 (INC_PC reg) nbs Rm
      in
      (FUNPOW (SNEXT NEXT_ARM6) n <|state := ARM6 (DP
                 (if (Rd = 15) \/ (Rd = Rm) then
                    REG_WRITE reg nbs 15 (pc + 4w)
                  else
                    REG_WRITE (REG_WRITE reg nbs 15 (pc + 4w)) nbs Rd
                      (if WORD_BIT 21 ireg then
                         rn
                       else
                         0w)) psr (pc + 4w) ireg alua rn dout)
              (CTRL pipea T pipeb T ireg T
                 ointstart F F obaselatch F mla_mul tn
                 F F F onfq ooonfq oniq oooniq pipeaabt pipebabt pipebabt dataabt2
                 aregn2 F T F sctrl psrfb (WORD_BITS 1 0 pc) ARB ARB orp
                 (WORD_BITS 1 0 rs) (WORD_BITS HB 2 rs) F (if WORD_BITS 1 0 rs = 2 then 1 else 0));
              inp := ADVANCE 1 i|> =
        (let mul = BITS 1 0 (WORD_BITS HB (2 * (n - 1)) rs)
         in
         let rd = RD_INVARIANT (WORD_BIT 21 ireg) rm rs rn (n - 1)
         and mshift = MSHIFT mla_mul (BORROW2 rs (n - 1)) mul (n - 1)
         and mul' = BITS 1 0 (WORD_BITS HB (2 * n) rs)
         and borrow2 = BORROW2 rs n
         in
         let rd' = RD_INVARIANT (WORD_BIT 21 ireg) rm rs rn n
         and newinst = MLA_MUL_DONE rs n
         in
         let nxtic = if newinst then
                       if ointstart' then swi_ex else DECODE_INST (w2n pipeb)
                     else mla_mul in 
          <| state := ARM6 (DP
                (if (Rd = 15) \/ (Rd = Rm) then
                   REG_WRITE reg nbs 15 (pc + 4w)
                 else
                   REG_WRITE (REG_WRITE reg nbs 15 (pc + 4w)) nbs Rd rd')
                (if (n = 0) \/ ~WORD_BIT 20 ireg \/ (Rd = 15) \/ (Rd = Rm) then psr else
                   CPSR_WRITE psr (SET_NZC (MSB rd',rd' = 0w,
                      FST (LSL rm mshift (CARRY (FST (DECODE_PSR cpsr))))) cpsr))
                (pc + 4w) (if newinst then pipeb else ireg)
                (if n = 0 then alua else
                   if (Rd = 15) \/ (Rd = Rm) then
                      REG_READ6 (REG_WRITE reg nbs 15 (pc + 4w)) nbs Rd else
                   rd)
                (if n = 0 then rn else rm << mshift) (if n = 0 then dout else rm))
             (CTRL
                pipea T (if newinst then pipea else pipeb) T
                (if newinst then pipeb else ireg) T ointstart' newinst newinst
                obaselatch' newinst nxtic
                (if newinst then t3 else tn)
                F F F onfq' ooonfq' oniq' oooniq' pipeaabt' pipebabt' (if newinst then iregabt' else pipebabt') dataabt'
                (if n = 0 then aregn2 else if ointstart' then aregn' else 2)
                (~(n = 0) /\ newinst) T F sctrl psrfb
                (if n = 0 then WORD_BITS 1 0 pc else WORD_BITS 1 0 (pc + n2w 4))
                (MASK nxtic (if newinst then t3 else tn) ARB ARB)
                ARB (if n = 0 then orp else ARB)
                mul' (WORD_BITS HB (2 * (n + 1)) rs)
                borrow2 (MSHIFT mla_mul borrow2 mul' (BITS 3 0 n))); inp := ADVANCE n (ADVANCE 1 i)|>))`,
  REPEAT STRIP_TAC
    THEN SIMP_TAC bool_ss [LET_THM]
    THEN ABBREV_TAC `Rm = WORD_BITS 3 0 ireg`
    THEN ABBREV_TAC `Rd = WORD_BITS 19 16 ireg`
    THEN ABBREV_TAC `rs = REG_READ6 reg nbs (WORD_BITS 11 8 ireg)`
    THEN ABBREV_TAC `rn = REG_READ6 reg nbs (WORD_BITS 15 12 ireg)`
    THEN ABBREV_TAC `rm = REG_READ6 (INC_PC reg) nbs Rm`
    THEN Induct_on `n`
    THEN1 (SIMP_TAC (arith_ss++STATE_INP_ss) [state_arm6_11,ctrl_11,iclass_distinct,
             io_onestepTheory.state_out_literal_11,FUNPOW,BORROW2_def,MSHIFT,RD_INVARIANT_ZERO,MASK_def,
             BITS_ZERO2,DONE_NEQ_ZERO,WORD_BITS_HB_0,GSYM WORD_BITS_def,io_onestepTheory.ADVANCE_ZERO]
            THEN PROVE_TAC [interrupt_exists])
    THEN REWRITE_TAC [FUNPOW_SUC]
    THEN Cases_on `n = 0`
    THENL [
      PAT_ASSUM `x ==> P` (K ALL_TAC)
        THEN ASM_REWRITE_TAC [FUNPOW]
        THEN REPEAT STRIP_TAC
        THEN PAT_ASSUM `Abbrev (pc = REG_READ6 reg usr 15)`
               (fn th => FULL_SIMP_TAC bool_ss [REG_READ_WRITE,TO_WRITE_READ6,th] THEN ASSUME_TAC th)
        THEN PURE_REWRITE_TAC [SNEXT_NEXT_ARM6,pairTheory.FST,pairTheory.SND] THEN MLA_MUL_TAC
        THEN ASM_SIMP_TAC (arith_ss++STATE_INP_ss) [COND_PAIR,ISPEC `FST` COND_RAND,ISPEC `SND` COND_RAND,
               IF_NEG,COMP_VAL_BIT2,BITS_X_SUB2_1,LSL_ZERO,ALUOUT_ADD,ALUOUT_SUB,COUNT1_ZERO,
               MUL1_SUC_1,BORROW2,GSYM WORD_BITS_def,MULX_DONE_ZERO,BITS_ZEROL,WORD_BITS_HB_0,
               RD_INVARIANT_ZERO,SND_LSL,ALUOUT_ALU_logic,NZ_ALU_logic,NZ_ADD,NZ_SUB,
               CARRY_LEM,state_arm6_11,dp_11]
        THEN `Rd < 16 /\ Rm < 16` by FULL_SIMP_TAC bool_ss [REGISTER_RANGES,markerTheory.Abbrev_def]
        THEN Cases_on `~(Rd = 15) /\ ~(Rd = Rm)`
        THEN FULL_SIMP_TAC stdi_ss [(GSYM o ISPEC `MSB`) COND_RAND,AREGN1_def,
                                    (GSYM o BETA_RULE o ISPEC `\x. x = 0w`) COND_RAND,
                                    REG_READ_WRITE,REG_WRITE_READ_NEQ,REG_WRITE_READ_NEQ_15,TO_WRITE_READ6,
                                    REG_WRITE_WRITE,IF_NEG,REGISTER_RANGES,RD_INVARIANT_ONE,RD_ONE,ctrl_11]
        THEN EXISTS_TAC `pipebabt`
        THEN EXISTS_TAC `if dataabt2 \/ ~BIT 6 (w2n cpsr) /\ ~ooonfq \/ pipebabt \/ ~BIT 7 (w2n cpsr) /\ ~oooniq then
                           AREGN1 F dataabt2 (~BIT 6 (w2n cpsr) /\ ~ooonfq) (~BIT 7 (w2n cpsr) /\ ~oooniq) F pipebabt
                         else 3`
        THEN POP_ASSUM_LIST (K ALL_TAC) THEN RW_TAC std_ss [AREGN1_def]
        THEN FULL_SIMP_TAC bool_ss [pred_setTheory.IN_INSERT,pred_setTheory.NOT_IN_EMPTY,
                                    num2exception_thm,exception_distinct],
      STRIP_TAC
        THEN `n <= MLA_MUL_DUR rs` by DECIDE_TAC
        THEN PAT_ASSUM `n ==> P` IMP_RES_TAC
        THEN ASM_SIMP_TAC arith_ss [NOT_DONE_SUC,BORROW2,GSYM io_onestepTheory.ADVANCE_COMP,ADD1]
        THEN POP_ASSUM (K ALL_TAC)
        THEN IMP_RES_TAC COUNT1_ID
        THEN PAT_ASSUM `Abbrev (pc = REG_READ6 reg usr 15)`
               (fn th => FULL_SIMP_TAC bool_ss [REG_READ_WRITE,TO_WRITE_READ6,th] THEN ASSUME_TAC th)
        THEN PURE_REWRITE_TAC [SNEXT_NEXT_ARM6,pairTheory.FST,pairTheory.SND] THEN MLA_MUL_TAC
        THEN ASM_SIMP_TAC (arith_ss++STATE_INP_ss) [GSYM io_onestepTheory.ADVANCE_COMP,
               COND_PAIR,ISPEC `FST` COND_RAND,ISPEC `SND` COND_RAND,
               (REWRITE_RULE [combinTheory.o_THM] o ISPEC `DECODE_MODE o WORD_BITS 4 0`) COND_RAND,
               ISPEC `CPSR_READ` COND_RAND,IF_NEG,COMP_VAL_BIT2,COUNT1,ADD1,BITS_X_SUB2,
               CPSR_WRITE_WRITE,CPSR_WRITE_READ,DECODE_MODE_SET_NZC,GSYM WORD_BITS_def,
               SPEC_MULX_DONE,ALUOUT_ADD,ALUOUT_SUB,SND_LSL,ALUOUT_ALU_logic,
               NZ_ALU_logic,NZ_ADD,NZ_SUB,CARRY_LEM,MUL1,MUL1_SUC,state_arm6_11]
        THEN `Rd < 16 /\ Rm < 16` by FULL_SIMP_TAC bool_ss [REGISTER_RANGES,markerTheory.Abbrev_def]
        THEN Cases_on `~(Rd = 15) /\ ~(Rd = Rm)`
        THEN FULL_SIMP_TAC bool_ss [dp_11,ctrl_11,RD_INVARIANT_SUC,(GSYM o ISPEC `MSB`) COND_RAND,
                                   (GSYM o BETA_RULE o ISPEC `\x. x = 0w`) COND_RAND,
                                   TO_WRITE_READ6,REG_READ_WRITE,REG_WRITE_READ_NEQ,REG_WRITE_READ_NEQ_15,
                                   SET_NZC_IDEM,REG_WRITE_WRITE,IF_NEG,REGISTER_RANGES,IF_FLAGS_SET_NZC_COND]
        THEN EXISTS_TAC `pipebabt'`
        THEN EXISTS_TAC `if dataabt' \/ ~BIT 6 (w2n cpsr) /\ ~ooonfq' \/ pipebabt' \/ ~BIT 7 (w2n cpsr) /\ ~oooniq' then
                           AREGN1 F dataabt' (~BIT 6 (w2n cpsr) /\ ~ooonfq') (~BIT 7 (w2n cpsr) /\ ~oooniq') F pipebabt'
                         else 3`
        THENL [
          PAT_ABBREV_TAC `bigc = CARRY (FST (DECODE_PSR (SET_NZC (a,b,c) x)))`
            THEN ABBREV_TAC `borrow2 = BIT 1 (WORD_BITS (2 * (n - 1) + 1) (2 * (n - 1)) rs)`
            THEN ABBREV_TAC `mul = WORD_BITS (2 * n + 1) (2 * n) rs`
            THEN ABBREV_TAC `mshift = n * 2 + (if borrow2 /\ (mul = 1) \/ ~borrow2 /\ (mul = 2) then 1 else 0)`
            THEN `~(mshift = 0)` by (UNABBREV_TAC `mshift` THEN RW_TAC arith_ss [])
            THEN POP_ASSUM (fn th => ASSUME_TAC (MATCH_MP LSL_CARRY_SUBST th))
            THEN POP_ASSUM (fn th => SUBST1_TAC (SPECL [`CARRY (FST (DECODE_PSR cpsr))`,`rm`,`bigc`] th))
            THEN REWRITE_TAC []
            THEN POP_ASSUM_LIST (K ALL_TAC)
            THEN RW_TAC stdi_ss [AREGN1_def]
            THEN FULL_SIMP_TAC std_ss [pred_setTheory.IN_INSERT,pred_setTheory.NOT_IN_EMPTY,
                                       num2exception_thm,exception_distinct],
          RW_TAC stdi_ss [AREGN1_def]
            THEN FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [num2exception_thm,exception_distinct],
          RW_TAC stdi_ss [AREGN1_def]
            THEN FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [num2exception_thm,exception_distinct]
        ]
    ]
);

(* -------------------------------------------------------- *)

val MLA_MUL_INVARIANT = save_thm("MLA_MUL_INVARIANT",
  SIMP_RULE std_ss [] MLA_MUL_INVARIANT);

val MLA_MUL_TN = save_thm("MLA_MUL_TN",
  (GEN_ALL o SIMP_RULE arith_ss [TO_WRITE_READ6,RD_INVARIANT_LAST,DONE_DUR,DUR_NEQ_ZERO] o
   INST [`n` |-> `MLA_MUL_DUR (REG_READ6 reg nbs (WORD_BITS 11 8 ireg))`] o SPEC_ALL) MLA_MUL_INVARIANT);

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val _ = export_theory();
