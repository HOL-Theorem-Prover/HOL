(* ===================================================================== *)
(* FILE          : lemmasScript.sml                                      *)
(* DESCRIPTION   : A collection of lemmas used to verify correctness     *)
(*                                                                       *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge              *)
(* DATE          : 2001 - 2005                                           *)
(* ===================================================================== *)

(* interactive use:
  app load ["intLib","word32Theory","word32Lib","armTheory","coreTheory"];
*)

open HolKernel boolLib bossLib Q numLib word32Lib arithmeticTheory
     bitsTheory word32Theory armTheory coreTheory;

val _ = new_theory "lemmas";

(* -------------------------------------------------------- *)

val _ = intLib.deprecate_int();

val std_ss = std_ss ++ boolSimps.LET_ss;
val arith_ss = arith_ss ++ boolSimps.LET_ss;

fun Cases_on_word tm = STRUCT_CASES_TAC (SPEC tm word_nchotomy);

(* -------------------------------------------------------- *)

val form_4tuple = save_thm("form_4tuple",
  (GEN_ALL o simpLib.SIMP_PROVE std_ss [])
    ``(a:bool # bool # bool # bool # word32) =
      (FST a,FST (SND a),FST (SND (SND a)),FST (SND (SND (SND a))),SND (SND (SND (SND a))))``);

val SNEXT_NEXT_ARM6 = save_thm("SNEXT_NEXT_ARM6",
  (ONCE_REWRITE_RULE [form_4tuple] o SIMP_RULE (srw_ss()) [] o
   SPEC `<|state := a; inp := i|>` o
   REWRITE_RULE [FUN_EQ_THM] o ISPEC `NEXT_ARM6`) io_onestepTheory.SNEXT_def
);

val COND_PAIR = save_thm("COND_PAIR",
  (GEN_ALL o PROVE []) ``(if e then (a,b) else (c,d)) =
                         (if e then a else c,if e then b else d)``
);

(* -------------------------------------------------------- *)

val MASK_MASK = store_thm("MASK_MASK",
  `!ic mask rp rp2.
     MASK ic t3 (MASK ic t3 mask rp) rp2 = MASK ic t3 mask rp`,
  RW_TAC std_ss [MASK_def]
);

(* -------------------------------------------------------- *)

val SND_LSL = store_thm("SND_LSL",
  `!n a c. SND (LSL a n c) = a << n`,
  RW_TAC arith_ss [LSL_def,ZERO_SHIFT2,LSL_LIMIT,HB_def]
);

val LSL_ZERO = save_thm("LSL_ZERO",(REWRITE_RULE [ZERO_SHIFT2] o SPEC `0`) SND_LSL);
val LSL_TWO = save_thm("LSL_TWO",SPEC `2` SND_LSL);

val SND_ROR = store_thm("SND_ROR",
  `!a n c. SND (ROR a n c) = a #>> n`,
  RW_TAC (bool_ss++boolSimps.LET_ss) [ROR_def,LSL_def,ZERO_SHIFT2,FUNPOW]
    THEN Cases_on_word `a`
    THEN SIMP_TAC arith_ss [ROR_THM,HB_def,WL_def,ADD1,BITS_ZERO3,MOD_MOD]
);

(* -------------------------------------------------------- *)

val DECODE_PSR = save_thm("DECODE_PSR",SIMP_RULE std_ss [GSYM WORD_BITS_def] DECODE_PSR_def);

(* -------------------------------------------------------- *)

val DIV1 = REDUCE_RULE DIV_ONE;

val IMMEDIATE_THM = store_thm("IMMEDIATE_THM",
  `!c i. IMMEDIATE c (WORD_BITS 11 0 i) =
           ROR (w32 (WORD_BITS 7 0 i)) (2 * WORD_BITS 11 8 i) c`,
  RW_TAC arith_ss [DIVMOD_2EXP_def,IMMEDIATE_def,WORD_BITS_COMP_THM,
    GSYM (SIMP_CONV arith_ss [BITS_THM,DIV1] ``BITS 7 0 n``),
    REDUCE_RULE (SPECL [`11`,`0`,`8`] WORD_BITS_DIV_THM)]
);

val IMMEDIATE_THM2 = store_thm("IMMEDIATE_THM2",
  `!c i. SND (IMMEDIATE c i) = SND (IMMEDIATE F i)`,
  RW_TAC std_ss [IMMEDIATE_def,ROR_def,DIVMOD_2EXP_def,LSL_def]
);

val SHIFT_IMMEDIATE_THM2 = store_thm("SHIFT_IMMEDIATE_THM2",
  `!r m c i. SHIFT_IMMEDIATE r m c (WORD_BITS 11 0 i) =
    let rm = REG_READ r m (WORD_BITS 3 0 i) in
       SHIFT_IMMEDIATE2 (WORD_BITS 11 7 i) (WORD_BITS 6 5 i) rm c`,
  RW_TAC arith_ss [SHIFT_IMMEDIATE_def,WORD_BITS_COMP_THM]
);

val SHIFT_REGISTER_THM2 = store_thm("SHIFT_REGISTER_THM2",
  `!r m c i. SHIFT_REGISTER r m c (WORD_BITS 11 0 i) =
               let shift = WORD_BITS 7 0 (REG_READ r m (WORD_BITS 11 8 i))
               and rm = REG_READ (INC_PC r) m (WORD_BITS 3 0 i) in
                 SHIFT_REGISTER2 shift (WORD_BITS 6 5 i) rm c`,
  RW_TAC arith_ss [SHIFT_REGISTER_def,WORD_BITS_COMP_THM]
);

(* -------------------------------------------------------- *)

fun case_i i =
  Cases_on [QUOTE ("opc="^(Int.toString i))]
    THENL [POP_ASSUM (fn th => REWRITE_TAC [th]) THEN REDUCE_TAC,ALL_TAC];

fun num_CONV_i i =
  FULL_SIMP_TAC bool_ss [num_CONV ((mk_numeral o Arbnum.fromInt) i)];

fun op_range i j f =
  if i > j then
    ALL_TAC
  else
    (f i) THEN (op_range (i+1) j f);

val TEST_OR_COMP_THM = prove(
  `!opc. opc < 16 ==> (TEST_OR_COMP opc = (BITS 3 2 opc = 2))`,
  REPEAT STRIP_TAC
    THEN SIMP_TAC arith_ss [TEST_OR_COMP_def,BITS_THM]
    THEN op_range 0 15 case_i 
    THEN op_range 1 15 num_CONV_i
    THEN RULE_ASSUM_TAC REDUCE_RULE
    THEN SPOSE_NOT_THEN (K ALL_TAC) THEN REPEAT (POP_ASSUM MP_TAC)
    THEN intLib.COOPER_TAC
);

val RW_WORD_TAC = ASM_REWRITE_TAC [] THEN WORD_TAC;

val BV_TWO = prove(
  `!n. n < 4 ==> (BIT 1 n /\ ~BIT 0 n = (n = 2))`,
  REPEAT STRIP_TAC
    THEN Cases_on `n = 0` THEN1 RW_WORD_TAC
    THEN Cases_on `n = 1` THEN1 RW_WORD_TAC
    THEN Cases_on `n = 2` THEN1 RW_WORD_TAC
    THEN Cases_on `n = 3` THEN1 RW_WORD_TAC
    THEN FULL_SIMP_TAC arith_ss []
);

val TEST_OR_COMP_THM2 = store_thm("TEST_OR_COMP_THM2",
  `!i. (WORD_BITS 24 23 i = 2) = WORD_BIT 24 i /\ ~WORD_BIT 23 i`,
  STRIP_TAC
    THEN ASSUME_TAC (SPEC `i` (REDUCE_RULE (SPECL [`24`,`23`] WORD_BITSLT_THM)))
    THEN `WORD_BIT 24 i = BIT 1 (WORD_BITS 24 23 i)` by SIMP_TAC arith_ss [WORD_BITS_COMP_THM,WORD_BIT_THM,BIT_def]
    THEN `WORD_BIT 23 i = BIT 0 (WORD_BITS 24 23 i)` by SIMP_TAC arith_ss [WORD_BITS_COMP_THM,WORD_BIT_THM,BIT_def]
    THEN ASM_SIMP_TAC arith_ss [BV_TWO]
);

val TEST_OR_COMP_THM = store_thm("TEST_OR_COMP_THM",
  `!i. TEST_OR_COMP (WORD_BITS 24 21 i) = WORD_BIT 24 i /\ ~WORD_BIT 23 i`,
  ASSUME_TAC (REDUCE_RULE (SPECL [`24`,`21`] WORD_BITSLT_THM))
    THEN RW_TAC arith_ss [WORD_BITS_COMP_THM,TEST_OR_COMP_THM,TEST_OR_COMP_THM2]
);

val ARITHMETIC_LEM = prove(
  `!opc. opc < 16 ==> (ARITHMETIC opc =
      (BIT 2 opc \/ BIT 1 opc) /\ (~BIT 3 opc \/ ~BIT 2 opc))`,
  REPEAT STRIP_TAC
    THEN SIMP_TAC arith_ss [ARITHMETIC_def,BIT_def,BITS_THM]
    THEN op_range 0 15 case_i 
    THEN op_range 1 15 num_CONV_i
    THEN RULE_ASSUM_TAC REDUCE_RULE
    THEN SPOSE_NOT_THEN (K ALL_TAC) THEN REPEAT (POP_ASSUM MP_TAC)
    THEN intLib.COOPER_TAC
);

val ARITHMETIC_THM = store_thm("ARITHMETIC_THM",
  `!i. ARITHMETIC (WORD_BITS 24 21 i) =
           (WORD_BIT 23 i \/ WORD_BIT 22 i) /\ (~WORD_BIT 24 i \/ ~WORD_BIT 23 i)`,
  ASSUME_TAC (REDUCE_RULE (SPECL [`24`,`21`] WORD_BITSLT_THM))
    THEN RW_TAC arith_ss [ARITHMETIC_LEM,WORD_BIT_THM,BIT_def,WORD_BITS_COMP_THM]
);

val ARITHMETIC_THM2 = store_thm("ARITHMETIC_THM2",
  `!i. ~WORD_BIT 23 i /\ ~WORD_BIT 22 i \/ WORD_BIT 24 i /\ WORD_BIT 23 i = 
         ~ARITHMETIC (WORD_BITS 24 21 i)`,
   RW_TAC bool_ss [ARITHMETIC_THM]
);

(* -------------------------------------------------------- *)

val ADD4_ADD4 = store_thm("ADD4_ADD4",
  `(!a. a + 4w + 4w = a + 8w)`,
  SIMP_TAC arith_ss [GSYM WORD_ADD_ASSOC,ADD_EVAL]
);

val REGISTER_RANGES = save_thm("REGISTER_RANGES",
  let fun conj (a,b) = CONJ a b in
   foldl conj (DECIDE ``14 < 16 /\ 15 < 16``)
     (map REDUCE_RULE [SPECL [`19`,`16`] WORD_BITSLT_THM,
                       SPECL [`15`,`12`] WORD_BITSLT_THM,
                       SPECL [`11`,`8`] WORD_BITSLT_THM,
                       SPECL [`3`,`0`] WORD_BITSLT_THM])
  end
);

(* -------------------------------------------------------- *)

val mode_num2register_15 = GEN_ALL (SIMP_RULE arith_ss [SYM r15] (SPECL [`m`,`15`] mode_num2register_def));

val NOT_PC_THM = store_thm("NOT_PC_THM",
  `!m1 m2 n. n < 16 /\ ~(n = 15) ==> ~(mode_num2register m1 n = mode_num2register m2 15)`,
  RW_TAC arith_ss [mode_num2register_def,USER_def,mode_case_def,register2num_11,num2register_11]
    THEN Cases_on `m1`
    THEN FULL_SIMP_TAC arith_ss [mode_distinct,mode_case_def,num2register_11]
);

val READ_TO_READ6 = store_thm("READ_TO_READ6",
  `!r m n d. n < 16 ==> (REG_READ (REG_WRITE r usr 15 (d - 8w)) m n =
                         REG_READ6 (REG_WRITE r usr 15 d) m n)`,
  RW_TAC bool_ss [REG_READ_def,REG_READ6_def,FETCH_PC_def,REG_WRITE_def,mode_num2register_15]
    THEN ASM_SIMP_TAC arith_ss [SUBST_def,WORD_SUB_ADD]
    THEN SUBST_TAC [SYM (SPEC `m` mode_num2register_15)]
    THEN ASM_SIMP_TAC bool_ss [NOT_PC_THM]
);

val TO_WRITE_READ6 = store_thm("TO_WRITE_READ6",
  `(!r. FETCH_PC r = REG_READ6 r usr 15) /\
   (!r. INC_PC r = REG_WRITE r usr 15 (REG_READ6 r usr 15 + 4w)) /\
   (!r. SUB8_PC r = REG_WRITE r usr 15 (REG_READ6 r usr 15 - 8w)) /\
   (!r m d. REG_WRITE r m 15 d = REG_WRITE r usr 15 d) /\
   (!r m. REG_READ6 r m 15 = REG_READ6 r usr 15)`,
  RW_TAC bool_ss [mode_num2register_def,r15,REG_READ6_def,REG_WRITE_def,
    REG_READ_def,FETCH_PC_def,INC_PC_def,SUB8_PC_def]
);

(* -------------------------------------------------------- *)

val SUBST_EQ2 = store_thm("SUBST_EQ2",
  `!m a. m {.a <- m a.} = m`,
  STRIP_TAC THEN SIMP_TAC bool_ss [FUN_EQ_THM,SUBST_def]
);

val REG_WRITE_WRITE = store_thm("REG_WRITE_WRITE",
  `!r m n d1 d2.  REG_WRITE (REG_WRITE r m n d1) m n d2 = REG_WRITE r m n d2`,
  RW_TAC bool_ss [REG_WRITE_def,SUBST_EQ]
);

val REG_WRITE_COMMUTE_PC = store_thm("REG_WRITE_COMMUTE_PC",
  `!r m1 m2 n d p.
      n < 16 /\ ~(n = 15) ==>
      (REG_WRITE (REG_WRITE r m1 15 p) m2 n d =
       REG_WRITE (REG_WRITE r m2 n d) m1 15 p)`,
  RW_TAC bool_ss [REG_WRITE_def,SUBST_NE_COMMUTES,NOT_PC_THM]
);

val REG_READ_WRITE = store_thm("REG_READ_WRITE",
  `!r m n d. REG_READ6 (REG_WRITE r m n d) m n = d`,
  RW_TAC bool_ss [REG_READ6_def,REG_READ_def,REG_WRITE_def,FETCH_PC_def,mode_num2register_def,r15,SUBST_def]
);

val REG_WRITE_READ = store_thm("REG_WRITE_READ",
  `!r m n d. (REG_WRITE r m n (REG_READ6 r m n) = r)`,
  RW_TAC bool_ss [REG_READ6_def,REG_READ_def,REG_WRITE_def,FETCH_PC_def,mode_num2register_15,SUBST_EQ2]
);

val REG_WRITE_READ_NEQ = store_thm("REG_WRITE_READ_NEQ",
  `!r m n1 n2. n1 < 16 /\ n2 < 16 /\ ~(n1 = n2) ==>
                 (REG_READ6 (REG_WRITE r m n1 d) m n2 = REG_READ6 r m n2)`,
  Cases_on `m`
    THEN RW_TAC bool_ss [REG_READ6_def,REG_READ_def,FETCH_PC_def,USER_def,
           REG_WRITE_def,SUBST_def,mode_num2register_def]
    THEN FULL_SIMP_TAC arith_ss [r15,num2register_11]
    THEN `n2 + 16 < 31` by DECIDE_TAC
    THEN FULL_SIMP_TAC arith_ss [r15,num2register_11]
);

val REG_READ6_TO_READ_SUB8 = store_thm("REG_READ6_TO_READ_SUB8",
  `!r m n. n < 16 ==> (REG_READ6 r m n = REG_READ (SUB8_PC r) m n)`,
  RW_TAC bool_ss [TO_WRITE_READ6,READ_TO_READ6,REG_WRITE_READ]
);

(* -------------------------------------------------------- *)

val SUB8_INV = store_thm("SUB8_INV",
  `!r. SUB8_PC (ADD8_PC r) = r`,
  RW_TAC bool_ss [WORD_ADD_SUB,SUB8_PC_def,ADD8_PC_def,SUBST_EQ,SUBST_EQ2,SUBST_def]
);

(* -------------------------------------------------------- *)

val BIT_OPC = store_thm("BIT_OPC",
  `(!i. BIT 0 (WORD_BITS 24 21 i) = WORD_BIT 21 i) /\
   (!i. BIT 2 (WORD_BITS 24 21 i) = WORD_BIT 23 i) /\
   (!i. BIT 3 (WORD_BITS 24 21 i) = WORD_BIT 24 i)`,
  SIMP_TAC arith_ss [BIT_def,WORD_BIT_THM,WORD_BITS_COMP_THM]
);

(* -------------------------------------------------------- *)

val DECODE_INST_NOT_UNEXEC = store_thm("DECODE_INST_NOT_UNEXEC",
  `!n. ~(DECODE_INST n = unexec)`,
  RW_TAC std_ss [DECODE_INST_def,DIVMOD_2EXP_def]
);

(* -------------------------------------------------------- *)

val NOT_A_OR_B = store_thm("NOT_A_OR_B",
  `!A B. ~A \/ B = ~(A /\ ~B)`,
  RW_TAC bool_ss []
);

(* -------------------------------------------------------- *)

val WORD_BITS118_LEM = save_thm("WORD_BITS118_LEM",REDUCE_RULE (SPECL [`11`,`7`,`1`] WORD_BITS_DIV_THM));

val WORD_SLICE_COMP_MSR1 = prove(
  `!a. WORD_SLICE 27 8 a + WORD_BITS 7 0 a = WORD_BITS 27 0 a`,
  SIMP_TAC arith_ss [GSYM WORD_SLICE_ZERO_THM,WORD_SLICE_COMP_RWT]
);

val WORD_SLICE_COMP_MSR2 = prove(
  `!a. WORD_SLICE 31 28 a + WORD_SLICE 27 8 a = WORD_SLICE 31 8 a`,
  SIMP_TAC arith_ss [WORD_SLICE_COMP_RWT]
);

val CONCAT_MSR_THM = store_thm("CONCAT_MSR_THM",
  `(!a b. CONCAT_BYTES (WORD_BITS 31 28 a) (WORD_BITS 27 8 b) (WORD_BITS 7 0 b) =
          w32 (WORD_SLICE 31 28 a + WORD_BITS 27 0 b)) /\
   (!a b. CONCAT_BYTES (WORD_BITS 31 28 a) (WORD_BITS 27 8 b) (WORD_BITS 7 0 a) =
          w32 (WORD_SLICE 31 28 a + WORD_SLICE 27 8 b + WORD_BITS 7 0 a)) /\
   (!a b. CONCAT_BYTES (WORD_BITS 31 28 a) (WORD_BITS 27 8 a) (WORD_BITS 7 0 b) =
          w32 (WORD_SLICE 31 8 a + WORD_BITS 7 0 b))`,
   RW_TAC bool_ss [GSYM WORD_SLICE_THM,CONCAT_BYTES_def,
                   GSYM ADD_ASSOC,TIMES_2EXP_def,WORD_SLICE_COMP_MSR1]
     THEN REWRITE_TAC [ADD_ASSOC,WORD_SLICE_COMP_MSR2]
);

val IF_NEG = store_thm("IF_NEG",
  `!a b c. (if ~a then b else c) = (if a then c else b)`,
  PROVE_TAC []
);

val DISJ_TO_CONJ = store_thm("DISJ_TO_CONJ",
  `!a b c d. (~a /\ ~b) \/ (c /\ d) = ~((a \/ b) /\ (~c \/ ~d))`,
  RW_TAC bool_ss [DE_MORGAN_THM]
);

(* -------------------------------------------------------- *)

val DATA_PROC_IMP_NOT_BIT4 = store_thm("DATA_PROC_IMP_NOT_BIT4",
  `!i. (DECODE_INST (w2n i) = data_proc) /\ (~WORD_BIT 25 i) ==> ~BIT 4 (WORD_BITS 11 0 i)`,
  RW_TAC arith_ss [DECODE_INST_def,BIT_def,WORD_BITS_def,WORD_BITS_COMP_THM]
    THEN FULL_SIMP_TAC bool_ss [WORD_BIT_def,BIT_def]
);

val REG_SHIFT_IMP_BITS = store_thm("REG_SHIFT_IMP_BITS",
  `!i. (DECODE_INST (w2n i) = reg_shift) ==> ~WORD_BIT 25 i /\ BIT 4 (WORD_BITS 11 0 i)`,
  RW_TAC arith_ss [DECODE_INST_def,BIT_def,WORD_BITS_def,WORD_BITS_COMP_THM]
    THEN FULL_SIMP_TAC bool_ss [WORD_BIT_def,BIT_def]
);

val LDR_IMP_BITS = store_thm("LDR_IMP_BITS",
  `!i. (DECODE_INST (w2n i) = ldr) ==> WORD_BIT 20 i`,
  RW_TAC arith_ss [DECODE_INST_def,WORD_BIT_def]
);

val STR_IMP_BITS = store_thm("STR_IMP_BITS",
  `!i. (DECODE_INST (w2n i) = str) ==> ~WORD_BIT 20 i`,
  RW_TAC arith_ss [DECODE_INST_def,WORD_BIT_def]
);

(* -------------------------------------------------------- *)

val MOD_WL_0 = REWRITE_CONV [MOD_WL_THM,BITS_ZERO2] ``MOD_WL 0``;
val MOD_WL_SYM = (GSYM o SIMP_RULE arith_ss [GSYM MOD_2EXP_def,WL_def,HB_def]) MOD_WL_def;

val ALUOUT_ALU_logic = store_thm("ALUOUT_ALU_logic",
  `!a. SND (ALU_logic a) = a`,
  SIMP_TAC std_ss [ALU_logic_def]
);

val NZ_ALU_logic = store_thm("NZ_ALU_logic",
  `(!a. FST (FST (ALU_logic a)) = MSB a) /\
   (!a. FST (SND (FST (ALU_logic a))) = (a = 0w))`,
  REPEAT STRIP_TAC THEN Cases_on_word `a`
    THEN SIMP_TAC std_ss [ALU_logic_def,n2w_11,MOD_WL_0,w2n_EVAL]
);

val ALUOUT_ADD = store_thm("ALUOUT_ADD",
  `!a b. SND (ADD a b F) = a + b`,
  REPEAT STRIP_TAC THEN Cases_on_word `a` THEN Cases_on_word `b`
    THEN SIMP_TAC arith_ss [ADD_def,ALU_arith_def,DIVMOD_2EXP,SBIT_def,ADD_EVAL,
           MOD_WL_SYM,w2n_EVAL,GSYM MOD_ADD,MOD_WL_ELIM]
);

val NZ_ADD = store_thm("NZ_ADD",
  `(!a b. FST (FST (ADD a b F)) = MSB (a + b)) /\
   (!a b. FST (SND (FST (ADD a b F))) = (a + b = 0w))`,
  REPEAT STRIP_TAC THEN Cases_on_word `a` THEN Cases_on_word `b`
    THEN SIMP_TAC arith_ss [ADD_def,ALU_arith_def,DIVMOD_2EXP,SBIT_def,ADD_EVAL,
           MOD_WL_SYM,w2n_EVAL,GSYM MOD_ADD,MOD_WL_ELIM,n2w_11,MOD_WL_0]
);

val ALUOUT_ADD_CARRY = store_thm("ALUOUT_ADD_CARRY",
  `!a b. SND (ADD a b T) = a + b + w32 1`,
  REPEAT STRIP_TAC THEN Cases_on_word `a` THEN Cases_on_word `b`
    THEN RW_TAC arith_ss [ADD_def,ALU_arith_def,DIVMOD_2EXP,SBIT_def]
    THEN REWRITE_TAC [ADD_ASSOC,GSYM ADD_EVAL,MOD_WL_SYM,w2n_EVAL,GSYM MOD_ADD,MOD_WL_ELIM]
);

val ALUOUT_SUB = store_thm("ALUOUT_SUB",
  `!a b. SND (SUB a b T) = a - b`,
  REPEAT STRIP_TAC THEN Cases_on_word `a` THEN Cases_on_word `b`
    THEN SIMP_TAC arith_ss [SUB_def,ALU_arith_neg_def,DIVMOD_2EXP,SBIT_def,MOD_WL_SYM,
           word_sub,TWO_COMP_EVAL,ADD_EVAL,w2n_EVAL,GSYM MOD_ADD,MOD_WL_ELIM]
);

val NZ_SUB = store_thm("NZ_SUB",
  `(!a b. FST (FST (SUB a b T)) = MSB (a - b)) /\
   (!a b. FST (SND (FST (SUB a b T))) = (a - b = 0w))`,
  REPEAT STRIP_TAC THEN Cases_on_word `a` THEN Cases_on_word `b`
    THEN SIMP_TAC arith_ss [SUB_def,ALU_arith_neg_def,DIVMOD_2EXP,SBIT_def,MOD_WL_SYM,word_sub,
           TWO_COMP_EVAL,ADD_EVAL,w2n_EVAL,GSYM MOD_ADD,MOD_WL_ELIM,n2w_11,MOD_WL_0]
);

(* -------------------------------------------------------- *)

val lem = prove(
  `!n. ~(HB < n) ==> (n MOD WL = n)`,
  RW_TAC bool_ss [NOT_LESS,WL_def,LESS_MOD,LESS_EQ_IMP_LESS_SUC]
);

val SLICE_ROR_THM = store_thm("SLICE_ROR_THM",
  `!h l a. w32 (WORD_SLICE h l a) #>> l = w32 (WORD_BITS h l a)`,
  REPEAT STRIP_TAC
    THEN Cases_on `l = 0` THEN1 ASM_REWRITE_TAC [WORD_SLICE_ZERO_THM,ZERO_SHIFT2]
    THEN Cases_on_word `a`
    THEN RW_TAC arith_ss [MIN_DEF,WORD_SLICE_def,WORD_BITS_def,BITS_COMP_THM2,SLICE_THM,w2n_EVAL,MOD_WL_THM]
    THENL [
      Cases_on `HB < l` THEN1 ASM_SIMP_TAC arith_ss [BITS_ZERO,ZERO_SHIFT]
        THEN RW_TAC arith_ss [ROR_THM,BITS_ZERO3,ADD1,ZERO_LT_TWOEXP,MOD_EQ_0,lem]
        THEN REWRITE_TAC [GSYM SLICE_THM,BITS_SLICE_THM],
      Cases_on `h < l` THEN1 ASM_SIMP_TAC arith_ss [BITS_ZERO,ZERO_SHIFT]
        THEN `l <= HB` by DECIDE_TAC
        THEN RW_TAC arith_ss [ROR_THM,BITS_ZERO3,ADD1,ZERO_LT_TWOEXP,MOD_EQ_0,lem]
        THEN ASM_SIMP_TAC arith_ss [GSYM SLICE_THM,BITS_SLICE_THM2]
    ]
);

(* -------------------------------------------------------- *)

val UP_DOWN_THM = store_thm("UP_DOWN_THM",
  `!b x y. (if b then x + y else x - y) = UP_DOWN b x y`,
  RW_TAC bool_ss [UP_DOWN_def]
);

(* -------------------------------------------------------- *)

val ONE_COMP_THREE_ADD = store_thm("ONE_COMP_THREE_ADD",
  `!a. a - 8w + 4w = NOT 3w + a`,
  GEN_REWRITE_TAC (ONCE_DEPTH_CONV o RAND_CONV) empty_rewrites  [WORD_ADD_COMM]
    THEN RW_TAC bool_ss [WORD_NOT,word_1]
    THEN WORD_TAC
    THEN REWRITE_TAC [GSYM WORD_ADD_ASSOC]
    THEN WORD_TAC
);

(* -------------------------------------------------------- *)

val MIN_31_5 = simpLib.SIMP_PROVE arith_ss [] ``MIN 31 5 = 5``;
val MIN_27_5 = simpLib.SIMP_PROVE arith_ss [] ``MIN 27 5 = 5``;
val MIN_31_27 = simpLib.SIMP_PROVE arith_ss [] ``MIN 31 27 = 27``;

val FACTOR_NZCV = prove(
  `!a b c d.
     SBIT a 31 + SBIT b 30 + SBIT c 29 + SBIT d 28 =
     (SBIT a 3 + SBIT b 2 + SBIT c 1 + SBIT d 0) * 2 ** SUC 27`,
  REWRITE_TAC [RIGHT_ADD_DISTRIB,SBIT_MULT] THEN SIMP_TAC arith_ss []
);

val SET_NZCV_IDEM = store_thm("SET_NZCV_IDEM",
  `!a b c. SET_NZCV a (SET_NZCV b c) = SET_NZCV a c`,
  Cases THEN Cases THEN Cases_on `r` THEN Cases_on `r'`
    THEN Cases_on `r` THEN Cases_on `r''`
    THEN RW_TAC bool_ss [ADD_0,BITS_SUM2,SET_NZCV_def,FACTOR_NZCV,WORD_BITS_def,MIN_31_27,
           MIN_IDEM,w2n_EVAL,MOD_WL_THM,HB_def,BITS_COMP_THM2]
);

val FACTOR_NZCV2 = prove(
  `(!a b c d.
      SBIT a 3 + (SBIT b 2 + (SBIT c 1 + SBIT d 0)) =
      (SBIT a 2 + SBIT b 1 + SBIT c 0) * 2 ** SUC 0 + SBIT d 0 * 2 ** 0) /\
   (!a b c d.
      SBIT a 3 + (SBIT b 2 + (SBIT c 1 + SBIT d 0)) =
      (SBIT a 1 + SBIT b 0) * 2 ** SUC 1 + (SBIT c 0 * 2 ** 1 + SBIT d 0)) /\
   (!a b c d.
     SBIT a 3 + (SBIT b 2 + (SBIT c 1 + SBIT d 0)) =
     SBIT a 0 * 2 ** SUC 2 + (SBIT b 0 * 2 ** 2 + (SBIT c 1 + SBIT d 0)))`,
  REWRITE_TAC [RIGHT_ADD_DISTRIB,SBIT_MULT] THEN SIMP_TAC arith_ss []
);

val lems = (CONJUNCTS FACTOR_NZCV2);

val FACTOR_NZCV3 = CONV_RULE (DEPTH_CONV reduceLib.SUC_CONV) FACTOR_NZCV;

val lt_thms = prove(
   `(!d. SBIT d 0 < 2 ** 1) /\
    (!c d. SBIT c 1 + SBIT d 0 < 2 ** 2) /\
    (!b c d. SBIT b 2 + (SBIT c 1 + SBIT d 0) < 2 ** 3)`,
  RW_TAC arith_ss [SBIT_def]
);
  
val lem = prove(
  `(!n. BIT 31 (w2n (n2w n)) = (BITS 3 3 (BITS 31 28 n) = 1)) /\
   (!n. BIT 30 (w2n (n2w n)) = (BITS 2 2 (BITS 31 28 n) = 1)) /\
   (!n. BIT 29 (w2n (n2w n)) = (BITS 1 1 (BITS 31 28 n) = 1)) /\
   (!n. BIT 28 (w2n (n2w n)) = (BITS 0 0 (BITS 31 28 n) = 1))`,
  RW_TAC arith_ss [w2n_EVAL,MOD_WL_THM,HB_def,BITS_COMP_THM2,BIT_def]
);

val BITSLT_27_0 =
  (REWRITE_RULE [SUB_0] o CONV_RULE (DEPTH_CONV reduceLib.SUC_CONV) o SPECL [`27`,`0`]) BITSLT_THM;

val DECODE_NZCV_SET_NZCV = store_thm("DECODE_NZCV_SET_NZCV",
   `(!a b c d n. BIT 31 (w2n (SET_NZCV (a,b,c,d) n)) = a) /\
    (!a b c d n. BIT 30 (w2n (SET_NZCV (a,b,c,d) n)) = b) /\
    (!a b c d n. BIT 29 (w2n (SET_NZCV (a,b,c,d) n)) = c) /\
    (!a b c d n. BIT 28 (w2n (SET_NZCV (a,b,c,d) n)) = d)`,
  REPEAT STRIP_TAC
    THEN SIMP_TAC bool_ss [lem,SIMP_RULE bool_ss [FACTOR_NZCV3] SET_NZCV_def,BITS_SUM,WORD_BITS_def,BITSLT_27_0]
    THEN SIMP_TAC bool_ss [SPEC `31` BITS_THM,ZERO_LT_TWOEXP,MULT_DIV,SUC_SUB]
    THEN SIMP_TAC arith_ss [(GSYM o numLib.REDUCE_RULE o SPEC `3`) BITS_ZERO3,BITS_COMP_THM2]
    THENL [
      REWRITE_TAC [(GEN_ALL o REWRITE_RULE [ADD] o SYM o SPECL [`a`,`3`,`0`]) SBIT_MULT],
      REWRITE_TAC [List.nth(lems,2)],
      REWRITE_TAC [List.nth(lems,1)],
      REWRITE_TAC [List.nth(lems,0)]
    ]
    THEN SIMP_TAC bool_ss [BITS_SUM2,BITS_SUM,lt_thms]
    THEN RW_TAC arith_ss [BITS_THM,SBIT_def]
);

val FACTOR_NZCV = prove(
  `(!a b c d.
     SBIT a 31 + SBIT b 30 + SBIT c 29 + SBIT d 28 =
     (SBIT a 23 + SBIT b 22 + SBIT c 21 + SBIT d 20) * 2 ** SUC 7) /\
   (!a b c d.
     SBIT a 31 + SBIT b 30 + SBIT c 29 + SBIT d 28 =
     (SBIT a 24 + SBIT b 23 + SBIT c 22 + SBIT d 21) * 2 ** SUC 6) /\
   (!a b c d.
     SBIT a 31 + SBIT b 30 + SBIT c 29 + SBIT d 28 =
     (SBIT a 26 + SBIT b 25 + SBIT c 24 + SBIT d 23) * 2 ** SUC 4)`,
  REWRITE_TAC [RIGHT_ADD_DISTRIB,SBIT_MULT] THEN SIMP_TAC arith_ss []
);

val lems = (CONJUNCTS FACTOR_NZCV);

val DECODE_IFMODE_SET_NZCV = store_thm("DECODE_IFMODE_SET_NZCV",
   `(!a b c d n. BIT 7 (w2n (SET_NZCV (a,b,c,d) n)) = BIT 7 (w2n n)) /\
    (!a b c d n. BIT 6 (w2n (SET_NZCV (a,b,c,d) n)) = BIT 6 (w2n n)) /\
    (!a b c d n. BITS 4 0 (w2n (SET_NZCV (a,b,c,d) n)) = BITS 4 0 (w2n n))`,
   REPEAT STRIP_TAC 
     THEN SIMP_TAC arith_ss [SET_NZCV_def,w2n_EVAL,MOD_WL_THM,HB_def,BITS_COMP_THM2,BIT_def,WORD_BITS_def]
     THENL List.tabulate(3,(fn i => SIMP_TAC bool_ss [ADD_ASSOC,List.nth(lems,i)]))
     THEN SIMP_TAC arith_ss [BITS_SUM2,BITS_COMP_THM2]
);

val FACTOR_NZCV = prove(
  `(!i f m n.
     mode_num m +
       (BITS 31 8 n * 256 +
        (BITS 5 5 n * 32 + (SBIT f 6 + SBIT i 7))) =
     (BITS 31 8 n * 2 ** 3 + BITS 5 5 n + (SBIT f 1 + SBIT i 2)) * 2 ** SUC 4 + mode_num m) /\
   (!i f m n.
     mode_num m +
       (BITS 31 8 n * 256 +
        (BITS 5 5 n * 32 + (SBIT f 6 + SBIT i 7))) =
     (BITS 31 8 n * 2 + SBIT i 0) * 2 ** SUC 6 + (SBIT f 0 * 2 ** 6 + (BITS 5 5 n * 32 + mode_num m))) /\
   (!i f m n.
     mode_num m +
       (BITS 31 8 n * 256 +
        (BITS 5 5 n * 32 + (SBIT f 6 + SBIT i 7))) =
     BITS 31 8 n * 2 ** SUC 7 + (SBIT i 0 * 2 ** 7 + (SBIT f 6 + BITS 5 5 n * 32 + mode_num m)))`,
  REWRITE_TAC [RIGHT_ADD_DISTRIB,SBIT_MULT] THEN SIMP_TAC arith_ss []
);

val lems = List.rev (CONJUNCTS FACTOR_NZCV);

val mode_num_lt = prove(
  `!m. mode_num m < 2 ** SUC 4`,
  Cases THEN RW_TAC std_ss [mode_num_def]
);

val lt_thms = prove(
  `(!m n. BITS 5 5 n * 32 + mode_num m < 2 ** 6) /\
   !f m n. SBIT f 6 + BITS 5 5 n * 32 + mode_num m < 2 ** 7`,
  RW_TAC bool_ss [SBIT_def]
    THEN ASSUME_TAC (SPEC `m` mode_num_lt)
    THEN ASSUME_TAC (SPECL [`5`,`5`,`n`] BITSLT_THM)
    THEN FULL_SIMP_TAC arith_ss []
);

val DECODE_IFMODE_SET_IFMODE = store_thm("DECODE_IFMODE_SET_IFMODE",
   `(!i f m n. BIT 7 (w2n (SET_IFMODE i f m n)) = i) /\
    (!i f m n. BIT 6 (w2n (SET_IFMODE i f m n)) = f) /\
    (!i f m n. BITS 4 0 (w2n (SET_IFMODE i f m n)) = mode_num m)`,
   REPEAT STRIP_TAC 
     THEN SIMP_TAC arith_ss [ADD_0,SET_IFMODE_def,w2n_EVAL,MOD_WL_THM,HB_def,
            BITS_COMP_THM2,BIT_def,WORD_BITS_def,WORD_SLICE_def,SLICE_THM]
     THENL List.tabulate(3,(fn i => SIMP_TAC bool_ss [BITS_SUM2,List.nth(lems,i)]))
     THEN SIMP_TAC bool_ss [mode_num_lt,lt_thms,BITS_ZEROL,BITS_SUM]
     THEN RW_TAC std_ss [SBIT_def,BITS_THM]
);

val lt_thms = prove(
  `(!i f m n. BITS 27 8 n * 2 ** 8 + SBIT i 7 + SBIT f 6 +
              BITS 5 5 n * 2 ** 5 + mode_num m < 2 ** 28) /\
   (!i f m n. BITS 28 8 n * 2 ** 8 + SBIT i 7 + SBIT f 6 +
              BITS 5 5 n * 2 ** 5 + mode_num m < 2 ** 29) /\
   (!i f m n. BITS 29 8 n * 2 ** 8 + SBIT i 7 + SBIT f 6 +
              BITS 5 5 n * 2 ** 5 + mode_num m < 2 ** 30) /\
   (!i f m n. BITS 30 8 n * 2 ** 8 + SBIT i 7 + SBIT f 6 +
              BITS 5 5 n * 2 ** 5 + mode_num m < 2 ** 31)`,
  RW_TAC bool_ss [SBIT_def]
    THEN ASSUME_TAC (SPEC `m` mode_num_lt)
    THEN MAP_EVERY (fn a => ASSUME_TAC (SPECL [a,`8`,`n`] BITSLT_THM)) [`30`,`29`,`28`,`27`]
    THEN ASSUME_TAC (SPECL [`5`,`5`,`n`] BITSLT_THM)
    THEN FULL_SIMP_TAC arith_ss []
);

val DECODE_NZCV_SET_IFMODE = store_thm("DECODE_NZCV_SET_IFMODE",
   `(!a b c d n. BIT 31 (w2n (SET_IFMODE i f m n)) = BIT 31 (w2n n)) /\
    (!a b c d n. BIT 30 (w2n (SET_IFMODE i f m n)) = BIT 30 (w2n n)) /\
    (!a b c d n. BIT 29 (w2n (SET_IFMODE i f m n)) = BIT 29 (w2n n)) /\
    (!a b c d n. BIT 28 (w2n (SET_IFMODE i f m n)) = BIT 28 (w2n n))`,
  REPEAT STRIP_TAC
     THEN SIMP_TAC bool_ss [ADD_0,SET_IFMODE_def,w2n_EVAL,MOD_WL_THM,HB_def,
            BITS_COMP_THM2,BIT_def,WORD_BITS_def,WORD_SLICE_def]
     THENL (
       map (fn (a,b) => SIMP_TAC std_ss [(GSYM o SIMP_RULE arith_ss [] o SPECL [`31`,a,b,`8`]) SLICE_COMP_RWT])
           [(`31`,`30`),(`30`,`29`),(`29`,`28`),(`28`,`27`)])
     THEN SIMP_TAC bool_ss [DECIDE ``(a:num) + b + c + d + e + f = a + (b + c + d + e + f)``,
            BITS_SUM,SLICE_THM,lt_thms]
     THEN SIMP_TAC bool_ss [BITS_THM,MULT_DIV,ZERO_LT_TWOEXP,MOD_MOD,MOD_MULT_MOD,
            simpLib.SIMP_PROVE arith_ss []  ``(2 ** (SUC 31 - 30) = 2 ** (SUC 30 - 30) * 2 ** 1) /\
                                              (2 ** (SUC 31 - 29) = 2 ** (SUC 29 - 29) * 2 ** 2) /\
                                              (2 ** (SUC 31 - 28) = 2 ** (SUC 28 - 28) * 2 ** 3)``]
);

val FACTOR_NZCV = prove(
  `!a b m n.
       BITS 31 8 n * 2 ** 8 + (SBIT a 7 + SBIT b 6 +
          BITS 5 5 n * 2 ** 5 + mode_num m) =
       (BITS 31 8 n * 2 ** 3 + SBIT a 2 + SBIT b 1 + BITS 5 5 n) * 2 ** 5 + mode_num m`,
  REWRITE_TAC [RIGHT_ADD_DISTRIB,SBIT_MULT] THEN SIMP_TAC arith_ss []
);

val FACTOR_NZCV2 = prove(
  `!a b n.
       BITS 31 8 n * 2 ** (3 + 5) + SBIT a 2 * 2 ** 5 + SBIT b 1 * 2 ** 5 =
       (BITS 31 8 n * 2 ** 2 + SBIT a 1 + SBIT b 0) * 2 ** SUC 5`,
  REWRITE_TAC [RIGHT_ADD_DISTRIB,SBIT_MULT] THEN SIMP_TAC arith_ss []
);

val lt_thm = prove(
  `!a b n m. SBIT a 7 + SBIT b 6 + BITS 5 5 n * 2 ** 5 + mode_num m < 2 ** 8`,
  RW_TAC bool_ss [SBIT_def]
    THEN ASSUME_TAC (SPEC `m` mode_num_lt)
    THEN ASSUME_TAC (SPECL [`5`,`5`,`n`] BITSLT_THM)
    THEN FULL_SIMP_TAC arith_ss []
);

val SET_IFMODE_IDEM = store_thm("SET_IFMODE_IDEM",
  `!a b c d e f g. SET_IFMODE a b c (SET_IFMODE d e f g) = SET_IFMODE a b c g`,
  RW_TAC bool_ss [SET_IFMODE_def,WORD_SLICE_def,SLICE_THM,ADD_0,w2n_EVAL,MOD_WL_THM,HB_def,MIN_IDEM,
     BITS_COMP_THM2,BITS_SUM,lt_thm,DECIDE ``(a:num) + b + c + d + e = a + (b + c + d + e)``]
   THEN SIMP_TAC bool_ss [CONV_RULE (DEPTH_CONV reduceLib.SUC_CONV) mode_num_lt,FACTOR_NZCV,BITS_SUM]
   THEN SIMP_TAC bool_ss [RIGHT_ADD_DISTRIB,GSYM MULT_ASSOC,GSYM EXP_ADD]
   THEN SIMP_TAC bool_ss [FACTOR_NZCV2,BITS_SUM2,MIN_31_5]
   THEN SIMP_TAC bool_ss [RIGHT_ADD_DISTRIB,SBIT_MULT,GSYM MULT_ASSOC,GSYM EXP_ADD,GSYM SLICE_THM]
   THEN CONV_TAC (DEPTH_CONV reduceLib.SUC_CONV) THEN CONV_TAC (DEPTH_CONV reduceLib.ADD_CONV)
   THEN SIMP_TAC bool_ss [GSYM SLICE_THM]
   THEN SIMP_TAC arith_ss [SLICE_COMP_THM2]
);

val lt_thm = prove(
  `!a b n m. BITS 27 8 n * 2 ** 8 + SBIT a 7 + SBIT b 6 + BITS 5 5 n * 2 ** 5 + mode_num m < 2 ** SUC 27`,
  RW_TAC bool_ss [SBIT_def]
    THEN ASSUME_TAC (SPEC `m` mode_num_lt)
    THEN ASSUME_TAC (SPECL [`27`,`8`,`n`] BITSLT_THM)
    THEN ASSUME_TAC (SPECL [`5`,`5`,`n`] BITSLT_THM)
    THEN FULL_SIMP_TAC arith_ss []
);

val lt_thm2 = prove(
  `!a b c d. SBIT a 3 + SBIT b 2 + SBIT c 1 + SBIT d 0 < 2 ** (SUC 31 - 28)`,
  RW_TAC arith_ss [SBIT_def]
);

val SET_IFMODE_NZCV_SWP = store_thm("SET_IFMODE_NZCV_SWP",
  `!a b c d e. SET_IFMODE a b c (SET_NZCV d e) = SET_NZCV d (SET_IFMODE a b c e)`,
  NTAC 3 STRIP_TAC THEN Cases THEN Cases_on `r` THEN Cases_on `r'`
    THEN RW_TAC bool_ss [SET_IFMODE_def,SET_NZCV_def,GSYM WORD_SLICE_COMP_MSR2,WORD_BITS_def,
           WORD_SLICE_def,w2n_EVAL,MOD_WL_THM,HB_def,BITS_COMP_THM2]
    THEN SIMP_TAC bool_ss [SLICE_THM,BITS_COMP_THM2,ADD_0,MIN_IDEM,MIN_31_5,MIN_31_27,
           BITS_SUM,FACTOR_NZCV3,BITSLT_27_0]
    THEN SIMP_TAC bool_ss [DECIDE ``28 = SUC 27``,BITS_SUM2,
           DECIDE ``(a:num) + b + c + d + e + f = a + (b + c + d + e + f)``]
    THEN SIMP_TAC bool_ss [BITS_SUM2,lt_thm,BITS_ZEROL,
           simpLib.SIMP_PROVE arith_ss [] ``a * 2 ** SUC 27 = a * 2 ** 22 * 2 ** SUC 5``]
    THEN SIMP_TAC bool_ss [BITS_COMP_THM2,ADD_0,MIN_IDEM,MIN_27_5,GSYM MULT_ASSOC,GSYM EXP_ADD,
           DECIDE ``(22 + SUC 5 = 28) /\ (SUC 27 = 28)``]
    THEN SIMP_TAC bool_ss [SPEC `31` BITS_THM,MULT_DIV,ZERO_LT_TWOEXP,LESS_MOD,lt_thm2]
);

val DECODE_MODE_THM = store_thm("DECODE_MODE_THM",
  `!m psr x y. DECODE_MODE (WORD_BITS 4 0 (SET_IFMODE x y m psr)) = m`,
  Cases THEN RW_TAC arith_ss [WORD_BITS_def,DECODE_IFMODE_SET_IFMODE,DECODE_MODE_def,mode_num_def]
);

(* -------------------------------------------------------- *)

val SPSR_READ_THM = store_thm("SPSR_READ_THM",
  `!psr mode cpsr.
     (CPSR_READ psr = cpsr) ==>
     ((if USER mode then cpsr else SPSR_READ psr mode) = SPSR_READ psr mode)`,
  RW_TAC bool_ss [CPSR_READ_def,SPSR_READ_def,mode2psr_def,USER_def]
    THEN REWRITE_TAC [mode_case_def]
);

val CPSR_WRITE_READ = store_thm("CPSR_WRITE_READ",
  `(!psr m x. CPSR_READ (SPSR_WRITE psr m x) = CPSR_READ psr) /\
   (!psr x. CPSR_READ (CPSR_WRITE psr x) = x)`,
  RW_TAC bool_ss [CPSR_READ_def,CPSR_WRITE_def,SPSR_WRITE_def,SUBST_def,USER_def,mode2psr_def]
    THEN Cases_on `m`
    THEN FULL_SIMP_TAC bool_ss [mode_case_def,psrs_distinct]
);

val CPSR_READ_WRITE = store_thm("CPSR_READ_WRITE",
  `(!psr. CPSR_WRITE psr (CPSR_READ psr) = psr) /\
   (!psr mode. USER mode ==> (CPSR_WRITE psr (SPSR_READ psr mode) = psr))`,
  RW_TAC bool_ss [CPSR_READ_def,CPSR_WRITE_def,SPSR_READ_def,SUBST_EQ2,USER_def,mode2psr_def]
    THEN REWRITE_TAC [mode_case_def,SUBST_EQ2]
);

val CPSR_WRITE_WRITE = store_thm("CPSR_WRITE_WRITE",
  `!psr a b. CPSR_WRITE (CPSR_WRITE psr a) b = CPSR_WRITE psr b`,
  SIMP_TAC bool_ss [CPSR_WRITE_def,SUBST_EQ]
);

val USER_usr = save_thm("USER_usr",simpLib.SIMP_PROVE bool_ss [USER_def] ``USER usr``);

val PSR_WRITE_COMM = store_thm("PSR_WRITE_COMM",
  `!psr m x y. SPSR_WRITE (CPSR_WRITE psr x) m y = CPSR_WRITE (SPSR_WRITE psr m y) x`,
  RW_TAC bool_ss [SPSR_WRITE_def,CPSR_WRITE_def,USER_def,mode2psr_def]
    THEN Cases_on `m`
    THEN FULL_SIMP_TAC bool_ss [mode_distinct,mode_case_def,psrs_distinct,SUBST_NE_COMMUTES]
);

(* -------------------------------------------------------- *)

val _ = export_theory();
