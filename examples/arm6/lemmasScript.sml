(* app load ["word32Theory","word32Lib","armTheory","coreTheory"]; *)
open HolKernel boolLib Q Parse bossLib numLib
     arithmeticTheory bitsTheory word32Theory word32Lib
     armTheory coreTheory;

infix 8 by;
infix THEN THENC THENL ++;

(* -------------------------------------------------------- *)

val _ = new_theory "lemmas";

(* -------------------------------------------------------- *)

val LSL_ZERO = store_thm("LSL_ZERO",
  `!a c. SND (LSL a 0 c) = a`,
  SIMP_TAC std_ss [LSL_def]
);

val LSL_TWO = store_thm("LSL_TWO",
  `!a c. SND (LSL a 2 c) = a << 2`,
  SIMP_TAC std_ss [LSL_def]
);

val ROR2_THM = store_thm("ROR2_THM",
  `!a n c. SND (ROR a n c) = a #>> n`,
  RW_TAC bool_ss [ROR_def,LSL_def,ZERO_SHIFT2,FUNPOW]
    THEN STRUCT_CASES_TAC (SPEC `a` word_nchotomy)
    THEN SIMP_TAC arith_ss [ROR_THM,HB_def,WL_def,ADD1,BITS_ZERO3,MOD_MOD]
);

val ROR2_THM2 = store_thm("ROR2_THM2",
  `!a n c. SND (ROR a n c) = SND (ROR a n F)`,
  RW_TAC std_ss [ROR_def,LSL_def]
);

(* -------------------------------------------------------- *)

val IMMEDIATE_THM = store_thm("IMMEDIATE_THM",
  `!c i. IMMEDIATE c (BITSw 11 0 i) =
           ROR (w32 (BITSw 7 0 i)) (2 * BITSw 11 8 i) c`,
  RW_TAC arith_ss [DIVMOD_2EXP_def,IMMEDIATE_def,BITSw_COMP_THM,
                   GSYM (SIMP_CONV arith_ss [BITS_THM,DIV1] ``BITS 7 0 n``),
                   REDUCE_RULE (SPECL [`11`,`0`,`8`] BITSw_DIV_THM)]
);

val SHIFT_IMMEDIATE_THM2 = store_thm("SHIFT_IMMEDIATE_THM2",
  `!r m c i. SHIFT_IMMEDIATE r m c (BITSw 11 0 i) =
    let rm = REG_READ r m (BITSw 3 0 i) in
       SHIFT_IMMEDIATE2 (BITSw 11 7 i) (BITSw 6 5 i) rm c`,
  RW_TAC arith_ss [SHIFT_IMMEDIATE_def,BITSw_COMP_THM]
);

val SHIFT_REGISTER_THM2 = store_thm("SHIFT_REGISTER_THM2",
  `!r m c i. SHIFT_REGISTER r m c (BITSw 11 0 i) =
               let shift = BITSw 7 0 (REG_READ r m (BITSw 11 8 i))
               and rm = REG_READ (INC_PC r) m (BITSw 3 0 i) in
                 SHIFT_REGISTER2 shift (BITSw 6 5 i) rm c`,
  RW_TAC arith_ss [SHIFT_REGISTER_def,BITSw_COMP_THM]
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

val TEST_OR_COMP_THM = store_thm("TEST_OR_COMP_THM",
  `!opc. opc < 16 ==> (TEST_OR_COMP opc = (BITS 3 2 opc = 2))`,
  REPEAT STRIP_TAC
    THEN SIMP_TAC arith_ss [TEST_OR_COMP_def,BITS_THM]
    THEN op_range 0 15 case_i 
    THEN op_range 1 15 num_CONV_i
    THEN FULL_SIMP_TAC bool_ss [NOT_ZERO_LT_ZERO]
    THEN IMP_RES_TAC LESS_NOT_SUC
    THEN REPEAT (PAT_ASSUM `~(a = b)` (K ALL_TAC))
    THEN RULE_ASSUM_TAC REDUCE_RULE
    THEN PAT_ASSUM `a < b` (fn th => FULL_SIMP_TAC bool_ss [th])
    THEN NTAC 13 (POP_ASSUM (K ALL_TAC))
    THEN DECIDE_TAC
);

val BV_TWO = store_thm("BV_TWO",
  `!n. n < 4 ==> (BIT 1 n /\ ~BIT 0 n = (n = 2))`,
  REPEAT STRIP_TAC
    THEN Cases_on `n = 0` THEN ASM_REWRITE_TAC []
    THENL [WORD_TAC,
       Cases_on `n = 1` THEN ASM_REWRITE_TAC []
         THENL [WORD_TAC,
            Cases_on `n = 2` THEN ASM_REWRITE_TAC []
              THENL [WORD_TAC,
                 Cases_on `n = 3` THEN ASM_REWRITE_TAC []
                   THENL [WORD_TAC,FULL_SIMP_TAC arith_ss []]
              ]
         ]
    ]
);

val TEST_OR_COMP_THM2 = store_thm("TEST_OR_COMP_THM2",
  `!i. (BITSw 24 23 i = 2) = BITw 24 i /\ ~BITw 23 i`,
  STRIP_TAC
    THEN ASSUME_TAC (SPEC `i` (REDUCE_RULE (SPECL [`24`,`23`] BITSwLT_THM)))
    THEN `BITw 24 i = BIT 1 (BITSw 24 23 i)` by SIMP_TAC arith_ss [BITSw_COMP_THM,BITw_THM,BIT_def]
    THEN `BITw 23 i = BIT 0 (BITSw 24 23 i)` by SIMP_TAC arith_ss [BITSw_COMP_THM,BITw_THM,BIT_def]
    THEN ASM_SIMP_TAC arith_ss [BV_TWO]
);

val TEST_OR_COMP_THM3 = store_thm("TEST_OR_COMP_THM3",
  `!i. TEST_OR_COMP (BITSw 24 21 i) = BITw 24 i /\ ~BITw 23 i`,
  ASSUME_TAC (REDUCE_RULE (SPECL [`24`,`21`] BITSwLT_THM))
    THEN RW_TAC arith_ss [BITSw_COMP_THM,TEST_OR_COMP_THM,TEST_OR_COMP_THM2]
);

val ARITHMETIC_THM = store_thm("ARITHMETIC_THM",
  `!opc. opc < 16 ==> (ARITHMETIC opc =
      (BIT 2 opc \/ BIT 1 opc) /\ (~BIT 3 opc \/ ~BIT 2 opc))`,
  REPEAT STRIP_TAC
    THEN SIMP_TAC arith_ss [ARITHMETIC_def,BIT_def,BITS_THM]
    THEN op_range 0 15 case_i 
    THEN op_range 1 15 num_CONV_i
    THEN FULL_SIMP_TAC bool_ss [NOT_ZERO_LT_ZERO]
    THEN IMP_RES_TAC LESS_NOT_SUC
    THEN REPEAT (PAT_ASSUM `~(a = b)` (K ALL_TAC))
    THEN RULE_ASSUM_TAC REDUCE_RULE
    THEN PAT_ASSUM `a < b` (fn th => FULL_SIMP_TAC bool_ss [th])
    THEN NTAC 13 (POP_ASSUM (K ALL_TAC))
    THEN DECIDE_TAC
);

val ARITHMETIC_THM2 = store_thm("ARITHMETIC_THM2",
  `!i. ARITHMETIC (BITSw 24 21 i) =
           (BITw 23 i \/ BITw 22 i) /\ (~BITw 24 i \/ ~BITw 23 i)`,
  ASSUME_TAC (REDUCE_RULE (SPECL [`24`,`21`] BITSwLT_THM))
    THEN RW_TAC arith_ss [ARITHMETIC_THM,BITw_THM,BIT_def,BITSw_COMP_THM]
);

(* -------------------------------------------------------- *)

val ADD4_SUB8_THM = store_thm("ADD4_SUB8_THM",
  `!a. a + w32 4 - w32 8 = a - w32 4`,
  STRIP_TAC THEN REWRITE_TAC [ADD_SUB_ASSOC] THEN WORD_TAC
);

val SUB8_ADD4_SUB8_THM = store_thm("SUB8_ADD4_SUB8_THM",
  `!a. a - w32 8 + w32 4 + w32 8 = a + w32 4`,
  REWRITE_TAC [GSYM ADD_SUB_SYM,ADD_SUBw]
);

val ADD4_ADD4_SUB8_THM = store_thm("ADD4_ADD4_SUB8_THM",
  `!a. a + w32 4 + w32 4 - w32 8 = a`,
  REWRITE_TAC [ADD_SUB_SYM,GSYM ADD_ASSOCw]
    THEN SIMP_TAC arith_ss [ADD_EVAL,GSYM ADD_SUB_SYM,ADD_SUBw]
);

(* -------------------------------------------------------- *)

val NOT_FA_EQ_FB = prove(
  `!a b f. ~(f a = f b) ==> ~(a = b)`,
  SPOSE_NOT_THEN STRIP_ASSUME_TAC
);

val WORD_ALIGN_LEM = store_thm("WORD_ALIGN_LEM",
  `!a b. ~(WORD_ALIGN a = WORD_ALIGN b) ==> ~(TO_W30 a = TO_W30 b)`,
  RW_TAC bool_ss [WORD_ALIGN_def,TO_W30_def,SLICEw_THM]
    THEN POP_ASSUM (fn th => ASSUME_TAC (REDUCE_RULE (MATCH_MP NOT_FA_EQ_FB th)))
    THEN RW_TAC arith_ss []
);

val MEM_WRITE_READ = store_thm("MEM_WRITE_READ",
  `!m d a1 a2 b.  ~(WORD_ALIGN a1 = WORD_ALIGN a2) ==>
      (MEMREAD (MEMWRITE m d a1 b) a2 = MEMREAD m a2)`,
  RW_TAC std_ss [WORD_ALIGN_def,MEMREAD_def,MEMWRITE_def,
                 WORD_ALIGN_LEM,MEM_WRITE_WORD_def,MEM_WRITE_BYTE_def,SUBST_def]
);

val MEMREAD_ALIGNED = store_thm("MEMREAD_ALIGNED",
  `!m a. MEM_READ_WORD m (WORD_ALIGN a) = MEMREAD m a`,
  SIMP_TAC arith_ss [MEM_READ_WORD_def,MEMREAD_def,WORD_ALIGN_def,TO_W30_def,
                     HB_def,BITS_EVAL,MODw_THM,BITS_COMP_THM,BITS_SLICEw_THM]
    THEN SIMP_TAC arith_ss [SLICEw_THM,BITSw_COMP_THM,MOD_EQ_0,ZERO_SHIFT2,
                            SIMP_RULE arith_ss [DIV1] (SPECL [`1`,`0`] BITS2_THM)]
);

(* -------------------------------------------------------- *)

val PC_WRITE_MODE_FREE = store_thm("PC_WRITE_MODE_FREE",
  `!r m p. REG_WRITE r m 15 p = REG_WRITE r usr 15 p`,
  Cases_on `r`
    THEN RW_TAC std_ss [REG_WRITE_def]
);

val PC_READ_MODE_FREE = store_thm("PC_READ_MODE_FREE",
  `!r m p. REG_READ6 r m 15 = REG_READ6 r usr 15`,
  RW_TAC std_ss [REG_READ6_def]
);

val REG_WRITE_READ_PC = store_thm("REG_WRITE_READ_PC",
  `!reg mode pc. REG_READ6 (REG_WRITE reg mode 15 pc) usr 15 = pc`,
  Cases_on `reg`
    THEN RW_TAC std_ss [REG_READ6_def,FETCH_PC_def,REG_WRITE_def,SUBST_def]
);

val REG_WRITE_WRITE_PC = store_thm("REG_WRITE_WRITE_PC",
  `!r m1 m2 p1 p2. REG_WRITE (REG_WRITE r m1 15 p1) m2 15 p2 = REG_WRITE r m2 15 p2`,
  Cases_on `r`
    THEN RW_TAC std_ss [REG_WRITE_def,SUBST_EQ]
);

val REG_WRITE_COMMUTES = store_thm("REG_WRITE_COMMUTES",
  `!r m1 m2 n d p. ~(n = 15) ==> (REG_WRITE (REG_WRITE r m1 15 p) m2 n d = REG_WRITE (REG_WRITE r m2 n d) m1 15 p)`,
  REPEAT STRIP_TAC
    THEN ONCE_REWRITE_TAC [PC_WRITE_MODE_FREE]
    THEN Cases_on `r`
    THEN RW_TAC std_ss [REG_WRITE_def,SUBST_NE_COMMUTES]
);

val REG_WRITE_READ_R14 = store_thm("REG_WRITE_READ_R14",
  `!r m m2 d x. REG_READ6 (REG_WRITE (REG_WRITE r m 14 d) m2 15 x) m 14 = d`,
  REPEAT STRIP_TAC
    THEN ONCE_REWRITE_TAC [PC_WRITE_MODE_FREE]
    THEN SIMP_TAC arith_ss [GSYM REG_WRITE_COMMUTES]
    THEN Cases_on `r`
    THEN RW_TAC arith_ss [REG_READ6_def,REG_READ_def,REG_WRITE_def,SUBST_def]
);

val REG_WRITE_WRITE_R14 = store_thm("REG_WRITE_WRITE_R14",
  `!r m d1 d2. REG_WRITE (REG_WRITE r m 14 d1) m 14 d2 = REG_WRITE r m 14 d2`,
  Cases_on `r`
    THEN RW_TAC std_ss [REG_WRITE_def,SUBST_EQ]
);

(* -------------------------------------------------------- *)

val BIT0_OPC = store_thm("BIT0_OPC",
  `!a. BIT 0 (BITSw 24 21 a) = BITw 21 a`,
  SIMP_TAC arith_ss [BIT_def,BITw_THM,BITSw_COMP_THM]
);
 
val BIT2_OPC = store_thm("BIT2_OPC",
  `!i. BIT 2 (BITSw 24 21 i) = BITw 23 i`,
  SIMP_TAC arith_ss [BIT_def,BITw_THM,BITSw_COMP_THM]
);

val BIT3_OPC = store_thm("BIT3_OPC",
  `!i. BIT 3 (BITSw 24 21 i) = BITw 24 i`,
  SIMP_TAC arith_ss [BIT_def,BITw_THM,BITSw_COMP_THM]
);

val ALUOUT_ALU_logic = store_thm("ALUOUT_ALU_logic",
  `!a. ALUOUT (ALU_logic a) = a`,
  REWRITE_TAC [ALUOUT_def,ALU_logic_def]
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
 
val SUBST_EQ2 = store_thm("SUBST_EQ2",
  `!m a. SUBST m (a,m a) = m`,
  STRIP_TAC THEN SIMP_TAC bool_ss [FUN_EQ_THM,SUBST_def]
);

val SUB8_INV = store_thm("SUB8_INV",
  `!r. SUB8_PC (ADD8_PC r) = r`,
  Cases_on `r`
    THEN RW_TAC std_ss [ADD_SUBw,SUB8_PC_def,ADD8_PC_def,SUBST_EQ,SUBST_EQ2,SUBST_def]
);

val FETCH_SUB8 = store_thm("FETCH_SUB8",
  `!r.  FETCH_PC (SUB8_PC r) = REG_READ6 r usr 15 - w32 8`,
  Cases_on `r`
    THEN RW_TAC std_ss [FETCH_PC_def,REG_READ6_def,SUB8_PC_def,SUBST_def]
);

val REG_READ_SUB8_PC = store_thm("REG_READ_SUB8_PC",
  `!r m n. REG_READ (SUB8_PC r) m n = REG_READ6 r m n`,
  Cases_on `r`
    THEN RW_TAC std_ss [SUBST_def,REG_READ_def,REG_READ6_def,SUB8_PC_def,FETCH_PC_def,
                        ONCE_REWRITE_RULE [ADD_SUB_SYM] ADD_SUBw]
);

val NOOP_REG = store_thm("NOOP_REG",
  `!r m.  INC_PC (SUB8_PC r) = SUB8_PC (REG_WRITE r m 15 (REG_READ6 r usr 15 + w32 4))`,
  Cases_on `r`
    THEN RW_TAC std_ss [INC_PC_def,SUB8_PC_def,REG_WRITE_def,REG_READ6_def,
                        FETCH_PC_def,SUBST_def,SUBST_EQ,ADD_SUB_SYM]
);

val OP_REG_LEM = store_thm("OP_REG_LEM",
  `!r m d. REG_WRITE (SUB8_PC r) m 15 d = SUB8_PC (REG_WRITE r m 15 (d + w32 4 + w32 4))`,
  ONCE_REWRITE_TAC [PC_WRITE_MODE_FREE]
    THEN Cases_on `r`
    THEN RW_TAC std_ss [REG_WRITE_def,SUB8_PC_def,SUBST_def,SUBST_EQ,ADD4_ADD4_SUB8_THM]
);

val INC_REG_LEM = store_thm("INC_REG_LEM",
  `!r m n d. ~(n = 15) ==> (REG_WRITE (SUB8_PC r) m n d = SUB8_PC (REG_WRITE r m n d))`,
  Cases_on `r`
    THEN RW_TAC std_ss [SUBST_NE_COMMUTES,FETCH_PC_def,SUB8_PC_def,REG_WRITE_def,SUBST_def]
);

val OP_REG = store_thm("OP_REG",
  `!r m d.  REG_WRITE (INC_PC (SUB8_PC r)) m 15 d =
                 SUB8_PC (REG_WRITE r m 15 (d + w32 4 + w32 4))`,
  ONCE_REWRITE_TAC [PC_WRITE_MODE_FREE]
    THEN SIMP_TAC std_ss [ONCE_REWRITE_RULE [PC_WRITE_MODE_FREE] NOOP_REG,
                          REG_WRITE_WRITE_PC,OP_REG_LEM]
);

val INC_WB_REG = store_thm("INC_WB_REG",
  `!r m d. INC_PC (SUB8_PC (REG_WRITE r m 15 d)) = SUB8_PC (REG_WRITE r m 15 (d + w32 4))`,
  ONCE_REWRITE_TAC [PC_WRITE_MODE_FREE]
    THEN SIMP_TAC std_ss [ONCE_REWRITE_RULE [PC_WRITE_MODE_FREE] NOOP_REG,
                          REG_WRITE_READ_PC,REG_WRITE_WRITE_PC]
);
 
val INC_PC_READ = store_thm("INC_PC_READ",
  `!r m n. REG_READ (INC_PC (SUB8_PC r)) m n =
             REG_READ6 (REG_WRITE r m 15 (REG_READ6 r usr 15 + w32 4)) m n`,
  ONCE_REWRITE_TAC [PC_WRITE_MODE_FREE]
    THEN SIMP_TAC std_ss [ONCE_REWRITE_RULE [PC_WRITE_MODE_FREE] NOOP_REG,REG_READ_SUB8_PC]
);

val OP_INC_REG = store_thm("OP_INC_REG",
  `!r m n. ~(n = 15) ==> (REG_WRITE (INC_PC (SUB8_PC r)) m n d =
       SUB8_PC (
         (REG_WRITE (REG_WRITE r m n d) m 15 (REG_READ6 r usr 15 + w32 4))))`,
  ONCE_REWRITE_TAC [PC_WRITE_MODE_FREE]
    THEN RW_TAC std_ss [ONCE_REWRITE_RULE [PC_WRITE_MODE_FREE] NOOP_REG,INC_REG_LEM,REG_WRITE_COMMUTES]
);

val OP_REG2 = store_thm("OP_REG2",
  `!r m m2 n x y.  REG_WRITE (REG_WRITE (INC_PC (SUB8_PC r)) m n x) m2 15 y =
                 SUB8_PC (REG_WRITE (REG_WRITE r m n x) m2 15 (y + w32 4 + w32 4))`,
  ONCE_REWRITE_TAC [PC_WRITE_MODE_FREE]
    THEN REPEAT STRIP_TAC
    THEN Cases_on `n = 15`
    THENL [
      ASM_SIMP_TAC std_ss [REG_WRITE_WRITE_PC] THEN REWRITE_TAC [OP_REG],
      ASM_SIMP_TAC std_ss [ONCE_REWRITE_RULE [PC_WRITE_MODE_FREE] NOOP_REG,REG_WRITE_COMMUTES,
                           REG_WRITE_WRITE_PC,INC_REG_LEM,OP_REG_LEM]
    ]
);
 
val OP_INC_REG2 = store_thm("OP_INC_REG2",
  `!r m m2 m3 n n2 x y.  ~(n = 15) /\ ~(n2 = 15) ==>
    (REG_WRITE (REG_WRITE (INC_PC (SUB8_PC r)) m n x) m2 n2 y =
     SUB8_PC (REG_WRITE (REG_WRITE (REG_WRITE r m n x) m2 n2 y)
                        m3 15 (REG_READ6 r usr 15 + w32 4)))`,
  ONCE_REWRITE_TAC [PC_WRITE_MODE_FREE]
    THEN RW_TAC std_ss [ONCE_REWRITE_RULE [PC_WRITE_MODE_FREE] NOOP_REG,INC_REG_LEM,REG_WRITE_COMMUTES]
);
 
val LINK_REG = store_thm("LINK_REG",
  `!r m m2 x y.  REG_WRITE (REG_WRITE (SUB8_PC r) m 14 x) usr 15 y =
                 SUB8_PC (REG_WRITE (REG_WRITE r m 14 x) m2 15 (y + w32 4 + w32 4))`,
  ONCE_REWRITE_TAC [PC_WRITE_MODE_FREE]
    THEN SIMP_TAC arith_ss [OP_REG_LEM,INC_REG_LEM]
);
 
val BRANCH_REG = store_thm("BRANCH_REG",
  `!r m y.  REG_WRITE (SUB8_PC r) usr 15 y =
                 SUB8_PC (REG_WRITE r m 15 (y + w32 4 + w32 4))`,
  ONCE_REWRITE_TAC [PC_WRITE_MODE_FREE]
    THEN SIMP_TAC arith_ss [OP_REG_LEM]
);
 
(* -------------------------------------------------------- *)

val MSR_ALU = store_thm("MSR_ALU",
  `!i alua alub c. BITw 21 i ==> (ALU6 mrs_msr t3 i alua alub c = ALU_logic alub)`,
  RW_TAC arith_ss [BITw_THM,BIT_def,BITSw_COMP_THM,ALU6_def]
);
 
val MRS_ALU = store_thm("MRS_ALU",
  `!i alua alub c. ~BITw 21 i ==> (ALU6 mrs_msr t3 i alua alub c = ALU_logic alua)`,
  RW_TAC arith_ss [BITw_THM,BIT_def,BITSw_COMP_THM,ALU6_def]
);

val ALUOUT_ALU_logic = store_thm("ALUOUT_ALU_logic",
  `!x. ALUOUT (ALU_logic x) = x`,
  RW_TAC std_ss [ALU_logic_def,ALUOUT_def]
);

val BITSw118_LEM = save_thm("BITSw118_LEM",REDUCE_RULE (SPECL [`11`,`7`,`1`] BITSw_DIV_THM));

val SLICEw_COMP_MSR1 = store_thm("SLICEw_COMP_MSR1",
  `!a. SLICEw 27 8 a + BITSw 7 0 a = BITSw 27 0 a`,
  RW_TAC arith_ss [DECIDE ``8 = SUC 7``,GSYM SLICEw_ZERO_THM,SLICEw_COMP_THM]
);

val SLICEw_COMP_MSR2 = store_thm("SLICEw_COMP_MSR2",
  `!a. SLICEw 31 28 a + SLICEw 27 8 a = SLICEw 31 8 a`,
  RW_TAC arith_ss [DECIDE ``28 = SUC 27``,SLICEw_COMP_THM]
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

val SPSR_READ_THM = store_thm("SPSR_READ_THM",
  `!psr mode. (if USER mode then CPSR_READ psr else SPSR_READ psr mode)
                    = SPSR_READ psr mode`,
  REPEAT STRIP_TAC
    THEN Cases_on `psr`
    THEN RW_TAC std_ss [CPSR_READ_def,SPSR_READ_def]
);

val NZCV_ALUOUT_THM = store_thm("NZCV_ALUOUT_THM",
  `!x. (FST (NZCV x) = FST x) /\ (FST (SND (NZCV x)) = FST (SND x)) /\
       (FST (SND (SND (NZCV x))) = FST (SND (SND x))) /\
       (SND (SND (SND (NZCV x))) = FST (SND (SND (SND x)))) /\
       (SND (SND (SND (SND x))) = ALUOUT x)`,
  REPEAT STRIP_TAC
    THEN Cases_on `x`
    THEN Cases_on `r`
    THEN Cases_on `r'`
    THEN Cases_on `r`
    THEN SIMP_TAC std_ss [NZCV_def,ALUOUT_def]
);

val DATA_PROC_IMP_NOT_BIT4 = store_thm("DATA_PROC_IMP_NOT_BIT4",
  `!i. (DECODE_INST (w2n i) = data_proc) /\ (~BITw 25 i) ==> ~BIT 4 (BITSw 11 0 i)`,
  RW_TAC arith_ss [DECODE_INST_def,BIT_def,BITSw_def,BITSw_COMP_THM]
    THEN FULL_SIMP_TAC bool_ss [BITw_def,BIT_def]
);

val REG_SHIFT_IMP_BITS = store_thm("REG_SHIFT_IMP_BITS",
  `!i. (DECODE_INST (w2n i) = reg_shift) ==> ~BITw 25 i /\ BIT 4 (BITSw 11 0 i)`,
  RW_TAC arith_ss [DECODE_INST_def,BIT_def,BITSw_def,BITSw_COMP_THM]
    THEN FULL_SIMP_TAC bool_ss [BITw_def,BIT_def]
);

val LDR_IMP_BITS = store_thm("LDR_IMP_BITS",
  `!i. (DECODE_INST (w2n i) = ldr) ==> BITw 20 i`,
  RW_TAC arith_ss [DECODE_INST_def,BITw_def]
);

val STR_IMP_BITS = store_thm("STR_IMP_BITS",
  `!i. (DECODE_INST (w2n i) = str) ==> ~BITw 20 i`,
  RW_TAC arith_ss [DECODE_INST_def,BITw_def]
);

(* -------------------------------------------------------- *)

val ALUOUT_ADD = store_thm("ALUOUT_ADD",
  `!a b. ALUOUT (ADD a b F) = a + b`,
  REPEAT STRIP_TAC
    THEN STRUCT_CASES_TAC (SPEC `a` word_nchotomy)
    THEN STRUCT_CASES_TAC (SPEC `b` word_nchotomy)
    THEN RW_TAC arith_ss [ALUOUT_def,ADD_def,ALU_arith_def,DIVMOD_2EXP_def,SBIT_def,
                          GSYM MODw_EVAL,ADD_EVAL,w2n_EVAL,GSYM MOD_ADD,MODw_ELIM]
);

val ALUOUT_SUB = store_thm("ALUOUT_SUB",
  `!a b. ALUOUT (SUB a b T) = a - b`,
  REPEAT STRIP_TAC
    THEN STRUCT_CASES_TAC (SPEC `a` word_nchotomy)
    THEN STRUCT_CASES_TAC (SPEC `b` word_nchotomy)
    THEN RW_TAC arith_ss [ALUOUT_def,SUB_def,ALU_arith_def,DIVMOD_2EXP_def,SBIT_def,GSYM MODw_EVAL,
                          word_sub,TWO_COMP_EVAL,ADD_EVAL,w2n_EVAL,GSYM MOD_ADD,MODw_ELIM]
);

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val lem = prove(
  `!n. ~(HB < n) ==> (n MOD WL = n)`,
  RW_TAC bool_ss [NOT_LESS,WL_def,LESS_MOD,LESS_EQ_IMP_LESS_SUC]
);

val SLICE_ROR_THM = store_thm("SLICE_ROR_THM",
  `!h l a. w32 (SLICEw h l a) #>> l = w32 (BITSw h l a)`,
  REPEAT STRIP_TAC
    THEN Cases_on `l = 0`
    THENL [
       ASM_REWRITE_TAC [SLICEw_ZERO_THM,ZERO_SHIFT2],
       STRUCT_CASES_TAC (SPEC `a` word_nchotomy)
         THEN RW_TAC arith_ss [MIN_DEF,SLICEw_def,BITSw_def,BITS_COMP_THM2,SLICE_THM,w2n_EVAL,MODw_THM]
         THENL [
           Cases_on `HB < l`
             THENL [
                ASM_SIMP_TAC arith_ss [BITS_ZERO,SYM w_0,ZERO_SHIFT],
                RW_TAC arith_ss [ROR_THM,BITS_ZERO3,ADD1,ZERO_LT_TWOEXP,MOD_EQ_0,lem]
                  THEN REWRITE_TAC [GSYM SLICE_THM,BITS_SLICE_THM]
             ],
           Cases_on `h < l`
             THENL [
                ASM_SIMP_TAC arith_ss [BITS_ZERO,SYM w_0,ZERO_SHIFT],
                `l <= HB` by DECIDE_TAC
                  THEN RW_TAC arith_ss [ROR_THM,BITS_ZERO3,ADD1,ZERO_LT_TWOEXP,MOD_EQ_0,lem]
                  THEN ASM_SIMP_TAC arith_ss [GSYM SLICE_THM,BITS_SLICE_THM2]
             ]
         ]
    ]
);

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)


val MUST_BE_THREE = store_thm("MUST_BE_THREE",
  `!a. ~(BITSw 1 0 a = 0) /\ ~(BITSw 1 0 a = 1) /\ ~(BITSw 1 0 a = 2) ==> (BITSw 1 0 a = 3)`,
  STRIP_TAC
    THEN ASSUME_TAC (SIMP_RULE arith_ss [] (SPECL [`1`,`0`,`a`] BITSwLT_THM))
    THEN RW_TAC arith_ss []
);

val LDR_SHIFT_REG_T3 = store_thm("LDR_SHIFT_REG_T3",
  `!i oareg sctrl busb c. BITw 25 i ==>
          (SHIFTER ldr t3 i oareg sctrl busb c =
               SHIFT_IMMEDIATE2 (BITSw 11 7 i) (BITSw 6 5 i) busb c)`,
  RW_TAC std_ss [SHIFTER_def]
);

val LDR_SHIFT_IMM_T3 = store_thm("LDR_SHIFT_IMM_T3",
  `!i oareg sctrl busb c. ~BITw 25 i ==>
          (SND (SHIFTER ldr t3 i oareg sctrl busb c) = busb)`,
  RW_TAC std_ss [SHIFTER_def,LSL_def]
);

val LDR_FIELD_T3 = store_thm("LDR_FIELD_T3",
  `!i oareg din.  FIELD ldr t3 i oareg din = w32 (BITSw 11 0 din)`,
  RW_TAC bool_ss [FIELD_def]
);

val LDR_ALU6_T5 = store_thm("LDR_ALU6_T5",
  `!i alua alub c.  ALUOUT (ALU6 ldr t5 i alua alub c) = alub`,
  RW_TAC std_ss [ALU6_def,ALUOUT_ALU_logic]
);

val SWP_ALU6_T = store_thm("SWP_ALU6_T",
  `!t i alua alub c.  ALUOUT (ALU6 swp t i alua alub c) = alub`,
  RW_TAC std_ss [ALU6_def,ALUOUT_ALU_logic]
);

val SWP_SHIFT = store_thm("SWP_SHIFT",
  `!a b c. SND (ROR a (8 * BITSw 1 0 b) c) = a #>> (8 * BITSw 1 0 b)`,
  REPEAT STRIP_TAC
    THEN ASSUME_TAC (SIMP_RULE arith_ss [] (SPECL [`1`,`0`,`b`] BITSwLT_THM))
    THEN `8 * BITSw 1 0 b < 32` by DECIDE_TAC
    THEN ASM_SIMP_TAC std_ss [ROR2_THM]
);

val MUST_BE_BIT21 = store_thm("MUST_BE_BIT21",
  `!i. ~(BITw 24 i /\ ~BITw 21 i) /\ BITw 24 i ==> BITw 21 i`,
  PROVE_TAC []
);

(* -------------------------------------------------------- *)

val ONE_COMPw_THREE_ADD = store_thm("ONE_COMPw_THREE_ADD",
  `!a. a - w32 8 + w32 4 = NOT (w32 3) + a`,
  GEN_REWRITE_TAC (ONCE_DEPTH_CONV o RAND_CONV) empty_rewrites  [ADD_COMMw]
    THEN RW_TAC bool_ss [ONE_COMP_TWO_COMP,w_1]
    THEN WORD_TAC
    THEN REWRITE_TAC [GSYM ADD_ASSOCw]
    THEN WORD_TAC
);
 
val CPSR_WRITE_READ = store_thm("CPSR_WRITE_READ",
  `(!psr m x. CPSR_READ (SPSR_WRITE psr m x) = CPSR_READ psr) /\
   (!psr x. CPSR_READ (CPSR_WRITE psr x) = x)`,
  REPEAT STRIP_TAC
    THEN Cases_on `psr`
    THEN RW_TAC std_ss [CPSR_READ_def,CPSR_WRITE_def,SPSR_WRITE_def,SUBST_def]
);

val DECODE_MODE_LEM = store_thm("DECODE_MODE_LEM",
  `!m psr. BITS 4 0 (w2n (SET_MODE m psr)) =
                if m = usr then 16 else
                if m = fiq then 17 else
                if m = irq then 18 else
                if m = svc then 19 else
                if m = abt then 23 else
                if m = und then 27 else 0`,
  SIMP_TAC arith_ss [SET_MODE_def,GSYM BITSw_def,BITS_EVAL,MODw_THM,HB_def,BITS_COMP_THM]
    THEN RW_TAC arith_ss [SLICEw_THM,SIMP_RULE arith_ss [DIV1] (SPECL [`4`,`0`] BITS2_THM),MOD_TIMES]
);

val DECODE_MODE_THM = store_thm("DECODE_MODE_THM",
  `!m psr x y. DECODE_MODE (w2n (SET_IFMODE x y m psr)) = m`,
  REPEAT STRIP_TAC
    THEN SIMP_TAC std_ss [SET_IFMODE_def,DECODE_MODE_def,DECODE_MODE_LEM]
    THEN Cases_on `m`
    THEN SIMP_TAC arith_ss [mode_distinct]
);
  
val PSR_WRITE_COMM = store_thm("PSR_WRITE_COMM",
  `!psr m x y. SPSR_WRITE (CPSR_WRITE psr x) m y = CPSR_WRITE (SPSR_WRITE psr m y) x`,
  Cases_on `psr`
    THEN RW_TAC std_ss [SPSR_WRITE_def,CPSR_WRITE_def]
);

(* -------------------------------------------------------- *)
 
val _ = export_theory();
