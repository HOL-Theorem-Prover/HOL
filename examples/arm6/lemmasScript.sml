(* app load ["word32Theory","word32Lib","armTheory","coreTheory","intLib"]; *)
open HolKernel boolLib bossLib Q numLib
     arithmeticTheory bitsTheory word32Theory word32Lib
     armTheory coreTheory;

(* -------------------------------------------------------- *)

val _ = new_theory "lemmas";

(* -------------------------------------------------------- *)

val _ = prefer_num();

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

val DIV1 = REDUCE_RULE DIV_ONE;

val IMMEDIATE_THM = store_thm("IMMEDIATE_THM",
  `!c i. IMMEDIATE c (WORD_BITS 11 0 i) =
           ROR (w32 (WORD_BITS 7 0 i)) (2 * WORD_BITS 11 8 i) c`,
  RW_TAC arith_ss [DIVMOD_2EXP_def,IMMEDIATE_def,WORD_BITS_COMP_THM,
                   GSYM (SIMP_CONV arith_ss [BITS_THM,DIV1] ``BITS 7 0 n``),
                   REDUCE_RULE (SPECL [`11`,`0`,`8`] WORD_BITS_DIV_THM)]
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

val TEST_OR_COMP_THM = store_thm("TEST_OR_COMP_THM",
  `!opc. opc < 16 ==> (TEST_OR_COMP opc = (BITS 3 2 opc = 2))`,
  REPEAT STRIP_TAC
    THEN SIMP_TAC arith_ss [TEST_OR_COMP_def,BITS_THM]
    THEN op_range 0 15 case_i 
    THEN op_range 1 15 num_CONV_i
    THEN RULE_ASSUM_TAC REDUCE_RULE
    THEN SPOSE_NOT_THEN (K ALL_TAC) THEN REPEAT (POP_ASSUM MP_TAC)
    THEN intLib.COOPER_TAC
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
  `!i. (WORD_BITS 24 23 i = 2) = WORD_BIT 24 i /\ ~WORD_BIT 23 i`,
  STRIP_TAC
    THEN ASSUME_TAC (SPEC `i` (REDUCE_RULE (SPECL [`24`,`23`] WORD_BITSLT_THM)))
    THEN `WORD_BIT 24 i = BIT 1 (WORD_BITS 24 23 i)` by SIMP_TAC arith_ss [WORD_BITS_COMP_THM,WORD_BIT_THM,BIT_def]
    THEN `WORD_BIT 23 i = BIT 0 (WORD_BITS 24 23 i)` by SIMP_TAC arith_ss [WORD_BITS_COMP_THM,WORD_BIT_THM,BIT_def]
    THEN ASM_SIMP_TAC arith_ss [BV_TWO]
);

val TEST_OR_COMP_THM3 = store_thm("TEST_OR_COMP_THM3",
  `!i. TEST_OR_COMP (WORD_BITS 24 21 i) = WORD_BIT 24 i /\ ~WORD_BIT 23 i`,
  ASSUME_TAC (REDUCE_RULE (SPECL [`24`,`21`] WORD_BITSLT_THM))
    THEN RW_TAC arith_ss [WORD_BITS_COMP_THM,TEST_OR_COMP_THM,TEST_OR_COMP_THM2]
);

val ARITHMETIC_THM = store_thm("ARITHMETIC_THM",
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

val ARITHMETIC_THM2 = store_thm("ARITHMETIC_THM2",
  `!i. ARITHMETIC (WORD_BITS 24 21 i) =
           (WORD_BIT 23 i \/ WORD_BIT 22 i) /\ (~WORD_BIT 24 i \/ ~WORD_BIT 23 i)`,
  ASSUME_TAC (REDUCE_RULE (SPECL [`24`,`21`] WORD_BITSLT_THM))
    THEN RW_TAC arith_ss [ARITHMETIC_THM,WORD_BIT_THM,BIT_def,WORD_BITS_COMP_THM]
);

(* -------------------------------------------------------- *)

val ADD4_SUB8_THM = store_thm("ADD4_SUB8_THM",
  `!a. a + w32 4 - w32 8 = a - w32 4`,
  STRIP_TAC THEN REWRITE_TAC [WORD_ADD_SUB_ASSOC] THEN WORD_TAC
);

(*
val SUB8_ADD4_SUB8_THM = store_thm("SUB8_ADD4_SUB8_THM",
  `!a. a - w32 8 + w32 4 + w32 8 = a + w32 4`,
  REWRITE_TAC [GSYM WORD_ADD_SUB_SYM,WORD_ADD_SUB]
);
*)

val ADD4_ADD4_SUB8_THM = store_thm("ADD4_ADD4_SUB8_THM",
  `!a. a + w32 4 + w32 4 - w32 8 = a`,
  REWRITE_TAC [WORD_ADD_SUB_SYM,GSYM WORD_ADD_ASSOC]
    THEN SIMP_TAC arith_ss [ADD_EVAL,GSYM WORD_ADD_SUB_SYM,WORD_ADD_SUB]
);

(* -------------------------------------------------------- *)

val NOT_FA_EQ_FB = prove(
  `!a b f. ~(f a = f b) ==> ~(a = b)`,
  SPOSE_NOT_THEN STRIP_ASSUME_TAC
);

val WORD_ALIGN_LEM = store_thm("WORD_ALIGN_LEM",
  `!a b. ~(WORD_ALIGN a = WORD_ALIGN b) ==> ~(TO_W30 a = TO_W30 b)`,
  RW_TAC arith_ss [WORD_ALIGN_def,TO_W30_def,WORD_SLICE_THM]
);

val MEM_WRITE_READ = store_thm("MEM_WRITE_READ",
  `!m d a1 a2 b.  ~(WORD_ALIGN a1 = WORD_ALIGN a2) ==>
      (MEMREAD (MEM_WRITE b m d a1) a2 = MEMREAD m a2)`,
  RW_TAC std_ss [WORD_ALIGN_def,MEMREAD_def,MEM_WRITE_def,
                 WORD_ALIGN_LEM,MEM_WRITE_WORD_def,MEM_WRITE_BYTE_def,SUBST_def]
);

(*
val MEMREAD_ALIGNED = store_thm("MEMREAD_ALIGNED",
  `!m a. MEM_READ_WORD m (WORD_ALIGN a) = MEMREAD m a`,
  SIMP_TAC arith_ss [MEM_READ_WORD_def,MEMREAD_def,WORD_ALIGN_def,TO_W30_def,
                     HB_def,BITS_EVAL,MOD_WL_THM,BITS_COMP_THM,WORD_BITS_SLICE_THM]
    THEN SIMP_TAC arith_ss [WORD_SLICE_THM,WORD_BITS_COMP_THM,MOD_EQ_0,ZERO_SHIFT2,
                            SIMP_RULE arith_ss [DIV1] (SPECL [`1`,`0`] BITS_THM2)]
);
*)

(* -------------------------------------------------------- *)

val REGISTER_RANGES = save_thm("REGISTER_RANGES",
  let fun conj (a,b) = CONJ a b in
   foldl conj (DECIDE ``14 < 16``)
     (map REDUCE_RULE [SPECL [`19`,`16`] WORD_BITSLT_THM,
                       SPECL [`15`,`12`] WORD_BITSLT_THM,
                       SPECL [`11`,`8`] WORD_BITSLT_THM,
                       SPECL [`3`,`0`] WORD_BITSLT_THM])
  end
);

(* -------------------------------------------------------- *)

val PC_WRITE_MODE_FREE = store_thm("PC_WRITE_MODE_FREE",
  `!r m p. REG_WRITE r m 15 p = REG_WRITE r usr 15 p`,
  RW_TAC bool_ss [mode_num2register_def,REG_WRITE_def]
);
 
val PC_READ_MODE_FREE = store_thm("PC_READ_MODE_FREE",
  `!r m p. REG_READ6 r m 15 = REG_READ6 r usr 15`,
  RW_TAC bool_ss [REG_READ6_def]
);
 
val REG_WRITE_READ_PC = store_thm("REG_WRITE_READ_PC",
  `!r m p. REG_READ6 (REG_WRITE r m 15 p) usr 15 = p`,
  RW_TAC bool_ss [REG_READ6_def,FETCH_PC_def,REG_WRITE_def,SUBST_def,
                  mode_num2register_def,r15,register2num_thm]
);
 
val REG_WRITE_WRITE_PC = store_thm("REG_WRITE_WRITE_PC",
  `!r m1 m2 p1 p2. REG_WRITE (REG_WRITE r m1 15 p1) m2 15 p2 = REG_WRITE r m2 15 p2`,
  RW_TAC bool_ss [REG_WRITE_def,SUBST_EQ,mode_num2register_def]
);
 
val NOT_PC_THM = store_thm("NOT_PC_THM",
  `!m1 m2 n. n < 16 /\ ~(n = 15) ==> ~(mode_num2register m1 n = mode_num2register m2 15)`,
  RW_TAC bool_ss [mode_num2register_def,USER_def]
    THEN FULL_SIMP_TAC arith_ss [mode_case_def,register2num_11,num2register_11]
    THEN Cases_on `m1`
    THEN FULL_SIMP_TAC arith_ss [mode_case_def,num2register_11]
);

val REG_WRITE_COMMUTES = store_thm("REG_WRITE_COMMUTES",
  `!r m1 m2 n d p.
      n < 16 /\ ~(n = 15) ==>
      (REG_WRITE (REG_WRITE r m1 15 p) m2 n d =
       REG_WRITE (REG_WRITE r m2 n d) m1 15 p)`,
  RW_TAC bool_ss [REG_WRITE_def,SUBST_NE_COMMUTES,NOT_PC_THM]
);
 
val REG_WRITE_READ_R14 = store_thm("REG_WRITE_READ_R14",
  `!r m m2 d x. REG_READ6 (REG_WRITE (REG_WRITE r m 14 d) m2 15 x) m 14 = d`,
  REPEAT STRIP_TAC
    THEN ONCE_REWRITE_TAC [PC_WRITE_MODE_FREE]
    THEN RW_TAC arith_ss [mode_num2register_def,REG_READ6_def,REG_READ_def,
                          REG_WRITE_def,SUBST_NE_COMMUTES,SUBST_def,USER_def]
    THEN Cases_on `m`
    THEN FULL_SIMP_TAC arith_ss [mode_case_def,mode_distinct,GSYM mode_distinct,num2register_11,register2num_11]
);
 
val REG_WRITE_WRITE_R14 = store_thm("REG_WRITE_WRITE_R14",
  `!r m d1 d2. REG_WRITE (REG_WRITE r m 14 d1) m 14 d2 = REG_WRITE r m 14 d2`,
  RW_TAC bool_ss [REG_WRITE_def,SUBST_EQ,USER_def,mode_num2register_def]
);

(* -------------------------------------------------------- *)

val BIT0_OPC = store_thm("BIT0_OPC",
  `!a. BIT 0 (WORD_BITS 24 21 a) = WORD_BIT 21 a`,
  SIMP_TAC arith_ss [BIT_def,WORD_BIT_THM,WORD_BITS_COMP_THM]
);
 
val BIT2_OPC = store_thm("BIT2_OPC",
  `!i. BIT 2 (WORD_BITS 24 21 i) = WORD_BIT 23 i`,
  SIMP_TAC arith_ss [BIT_def,WORD_BIT_THM,WORD_BITS_COMP_THM]
);

val BIT3_OPC = store_thm("BIT3_OPC",
  `!i. BIT 3 (WORD_BITS 24 21 i) = WORD_BIT 24 i`,
  SIMP_TAC arith_ss [BIT_def,WORD_BIT_THM,WORD_BITS_COMP_THM]
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
  RW_TAC bool_ss [WORD_ADD_SUB,SUB8_PC_def,ADD8_PC_def,SUBST_EQ,SUBST_EQ2,SUBST_def]
);
 
val FETCH_SUB8 = store_thm("FETCH_SUB8",
  `!r.  FETCH_PC (SUB8_PC r) = REG_READ6 r usr 15 - w32 8`,
  RW_TAC bool_ss [FETCH_PC_def,REG_READ6_def,SUB8_PC_def,SUBST_def]
);
 
val mode_num2register_15 = GEN_ALL (SIMP_RULE arith_ss [SYM r15] (SPECL [`m`,`15`] mode_num2register_def));

val REG_READ_SUB8_PC = store_thm("REG_READ_SUB8_PC",
  `!r m n. n < 16 ==> (REG_READ (SUB8_PC r) m n = REG_READ6 r m n)`,
  RW_TAC bool_ss [REG_READ_def,REG_READ6_def,SUB8_PC_def,FETCH_PC_def]
    THEN ASM_SIMP_TAC arith_ss [SUBST_def,WORD_SUB_ADD]
    THEN SUBST_TAC [SYM (SPEC `m` mode_num2register_15)]
    THEN ASM_SIMP_TAC bool_ss [NOT_PC_THM]
);
 
val NOOP_REG = store_thm("NOOP_REG",
  `!r m.  INC_PC (SUB8_PC r) = SUB8_PC (REG_WRITE r m 15 (REG_READ6 r usr 15 + w32 4))`,
  RW_TAC bool_ss [INC_PC_def,SUB8_PC_def,REG_WRITE_def,REG_READ6_def,mode_num2register_def,
                  SYM r15,FETCH_PC_def,SUBST_def,SUBST_EQ,WORD_ADD_SUB_SYM]
);
 
val OP_REG_LEM = store_thm("OP_REG_LEM",
  `!r m d. REG_WRITE (SUB8_PC r) m 15 d = SUB8_PC (REG_WRITE r m 15 (d + w32 4 + w32 4))`,
  RW_TAC bool_ss [mode_num2register_def,SYM r15,REG_WRITE_def,
                  SUB8_PC_def,SUBST_def,SUBST_EQ,ADD4_ADD4_SUB8_THM]
);
 
val INC_REG_LEM = store_thm("INC_REG_LEM",
  `!r m n d. n < 16 /\ ~(n = 15) ==> (REG_WRITE (SUB8_PC r) m n d = SUB8_PC (REG_WRITE r m n d))`,
  RW_TAC bool_ss [FETCH_PC_def,SUB8_PC_def,REG_WRITE_def]
    THEN SUBST_TAC [SYM (SPEC `m` mode_num2register_15)]
    THEN ASM_SIMP_TAC bool_ss [SUBST_def,SUBST_NE_COMMUTES,NOT_PC_THM]
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
  `!r m n. n < 16 ==> (REG_READ (INC_PC (SUB8_PC r)) m n =
             REG_READ6 (REG_WRITE r m 15 (REG_READ6 r usr 15 + w32 4)) m n)`,
  ONCE_REWRITE_TAC [PC_WRITE_MODE_FREE]
    THEN SIMP_TAC bool_ss [ONCE_REWRITE_RULE [PC_WRITE_MODE_FREE] NOOP_REG,REG_READ_SUB8_PC]
);
 
val OP_INC_REG = store_thm("OP_INC_REG",
  `!r m n. n < 16 /\ ~(n = 15) ==> (REG_WRITE (INC_PC (SUB8_PC r)) m n d =
       SUB8_PC (REG_WRITE (REG_WRITE r m n d) m 15 (REG_READ6 r usr 15 + w32 4)))`,
  ONCE_REWRITE_TAC [PC_WRITE_MODE_FREE]
    THEN SIMP_TAC bool_ss [ONCE_REWRITE_RULE [PC_WRITE_MODE_FREE] NOOP_REG,INC_REG_LEM,REG_WRITE_COMMUTES]
);

val OP_REG2 = store_thm("OP_REG2",
  `!r m m2 n x y.  n < 16 ==>
         (REG_WRITE (REG_WRITE (INC_PC (SUB8_PC r)) m n x) m2 15 y =
          SUB8_PC (REG_WRITE (REG_WRITE r m n x) m2 15 (y + w32 4 + w32 4)))`,
  ONCE_REWRITE_TAC [PC_WRITE_MODE_FREE]
    THEN REPEAT STRIP_TAC
    THEN Cases_on `n = 15`
    THENL [
      ASM_SIMP_TAC bool_ss [REG_WRITE_WRITE_PC] THEN REWRITE_TAC [OP_REG],
      ASM_SIMP_TAC bool_ss [ONCE_REWRITE_RULE [PC_WRITE_MODE_FREE] NOOP_REG,REG_WRITE_COMMUTES,                           REG_WRITE_WRITE_PC,INC_REG_LEM,OP_REG_LEM]
    ]
);
 
val OP_INC_REG2 = store_thm("OP_INC_REG2",
  `!r m m2 m3 n n2 x y.  n < 16 /\ n2 < 16 /\ ~(n = 15) /\ ~(n2 = 15) ==>
    (REG_WRITE (REG_WRITE (INC_PC (SUB8_PC r)) m n x) m2 n2 y =
     SUB8_PC (REG_WRITE (REG_WRITE (REG_WRITE r m n x) m2 n2 y)
                        m3 15 (REG_READ6 r usr 15 + w32 4)))`,
  ONCE_REWRITE_TAC [PC_WRITE_MODE_FREE]
    THEN SIMP_TAC bool_ss [ONCE_REWRITE_RULE [PC_WRITE_MODE_FREE] NOOP_REG,INC_REG_LEM,REG_WRITE_COMMUTES]
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
  `!i alua alub c. WORD_BIT 21 i ==> (ALU6 mrs_msr t3 i alua alub c = ALU_logic alub)`,
  RW_TAC arith_ss [WORD_BIT_THM,BIT_def,WORD_BITS_COMP_THM,ALU6_def]
);
 
val MRS_ALU = store_thm("MRS_ALU",
  `!i alua alub c. ~WORD_BIT 21 i ==> (ALU6 mrs_msr t3 i alua alub c = ALU_logic alua)`,
  RW_TAC arith_ss [WORD_BIT_THM,BIT_def,WORD_BITS_COMP_THM,ALU6_def]
);

val ALUOUT_ALU_logic = store_thm("ALUOUT_ALU_logic",
  `!x. ALUOUT (ALU_logic x) = x`,
  RW_TAC std_ss [ALU_logic_def,ALUOUT_def]
);

val WORD_BITS118_LEM = save_thm("WORD_BITS118_LEM",REDUCE_RULE (SPECL [`11`,`7`,`1`] WORD_BITS_DIV_THM));

val WORD_SLICE_COMP_MSR1 = store_thm("WORD_SLICE_COMP_MSR1",
  `!a. WORD_SLICE 27 8 a + WORD_BITS 7 0 a = WORD_BITS 27 0 a`,
  SIMP_TAC arith_ss [GSYM WORD_SLICE_ZERO_THM,WORD_SLICE_COMP_RWT]
);

val WORD_SLICE_COMP_MSR2 = store_thm("WORD_SLICE_COMP_MSR2",
  `!a. WORD_SLICE 31 28 a + WORD_SLICE 27 8 a = WORD_SLICE 31 8 a`,
  SIMP_TAC arith_ss [GSYM WORD_SLICE_ZERO_THM,WORD_SLICE_COMP_RWT]
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
  RW_TAC bool_ss [CPSR_READ_def,SPSR_READ_def,mode2psr_def,USER_def]
    THEN REWRITE_TAC [mode_case_def]
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

val ALUOUT_ADD = store_thm("ALUOUT_ADD",
  `!a b. ALUOUT (ADD a b F) = a + b`,
  REPEAT STRIP_TAC
    THEN STRUCT_CASES_TAC (SPEC `a` word_nchotomy)
    THEN STRUCT_CASES_TAC (SPEC `b` word_nchotomy)
    THEN RW_TAC arith_ss [ALUOUT_def,ADD_def,ALU_arith_def,DIVMOD_2EXP,SBIT_def,
                          GSYM MOD_WL_EVAL,ADD_EVAL,w2n_EVAL,GSYM MOD_ADD,MOD_WL_ELIM]
);

val ALUOUT_SUB = store_thm("ALUOUT_SUB",
  `!a b. ALUOUT (SUB a b T) = a - b`,
  REPEAT STRIP_TAC
    THEN STRUCT_CASES_TAC (SPEC `a` word_nchotomy)
    THEN STRUCT_CASES_TAC (SPEC `b` word_nchotomy)
    THEN RW_TAC arith_ss [ALUOUT_def,SUB_def,ALU_arith_neg_def,DIVMOD_2EXP,SBIT_def,GSYM MOD_WL_EVAL,
                          word_sub,TWO_COMP_EVAL,ADD_EVAL,w2n_EVAL,GSYM MOD_ADD,MOD_WL_ELIM]
);

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val lem = prove(
  `!n. ~(HB < n) ==> (n MOD WL = n)`,
  RW_TAC bool_ss [NOT_LESS,WL_def,LESS_MOD,LESS_EQ_IMP_LESS_SUC]
);

val SLICE_ROR_THM = store_thm("SLICE_ROR_THM",
  `!h l a. w32 (WORD_SLICE h l a) #>> l = w32 (WORD_BITS h l a)`,
  REPEAT STRIP_TAC
    THEN Cases_on `l = 0`
    THENL [
       ASM_REWRITE_TAC [WORD_SLICE_ZERO_THM,ZERO_SHIFT2],
       STRUCT_CASES_TAC (SPEC `a` word_nchotomy)
         THEN RW_TAC arith_ss [MIN_DEF,WORD_SLICE_def,WORD_BITS_def,BITS_COMP_THM2,SLICE_THM,w2n_EVAL,MOD_WL_THM]
         THENL [
           Cases_on `HB < l`
             THENL [
                ASM_SIMP_TAC arith_ss [BITS_ZERO,SYM word_0,ZERO_SHIFT],
                RW_TAC arith_ss [ROR_THM,BITS_ZERO3,ADD1,ZERO_LT_TWOEXP,MOD_EQ_0,lem]
                  THEN REWRITE_TAC [GSYM SLICE_THM,BITS_SLICE_THM]
             ],
           Cases_on `h < l`
             THENL [
                ASM_SIMP_TAC arith_ss [BITS_ZERO,SYM word_0,ZERO_SHIFT],
                `l <= HB` by DECIDE_TAC
                  THEN RW_TAC arith_ss [ROR_THM,BITS_ZERO3,ADD1,ZERO_LT_TWOEXP,MOD_EQ_0,lem]
                  THEN ASM_SIMP_TAC arith_ss [GSYM SLICE_THM,BITS_SLICE_THM2]
             ]
         ]
    ]
);

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val LDR_SHIFT_REG_T3 = store_thm("LDR_SHIFT_REG_T3",
  `!i oareg sctrl busb c. WORD_BIT 25 i ==>
          (SHIFTER ldr t3 i oareg sctrl busb c =
               SHIFT_IMMEDIATE2 (WORD_BITS 11 7 i) (WORD_BITS 6 5 i) busb c)`,
  RW_TAC std_ss [SHIFTER_def]
);

val LDR_SHIFT_IMM_T3 = store_thm("LDR_SHIFT_IMM_T3",
  `!i oareg sctrl busb c. ~WORD_BIT 25 i ==>
          (SND (SHIFTER ldr t3 i oareg sctrl busb c) = busb)`,
  RW_TAC std_ss [SHIFTER_def,LSL_def]
);

val LDR_FIELD_T3 = store_thm("LDR_FIELD_T3",
  `!i oareg din.  FIELD ldr t3 i oareg din = w32 (WORD_BITS 11 0 din)`,
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
  `!a b c. SND (ROR a (8 * WORD_BITS 1 0 b) c) = a #>> (8 * WORD_BITS 1 0 b)`,
  REPEAT STRIP_TAC
    THEN ASSUME_TAC (SIMP_RULE arith_ss [] (SPECL [`1`,`0`,`b`] WORD_BITSLT_THM))
    THEN `8 * WORD_BITS 1 0 b < 32` by DECIDE_TAC
    THEN ASM_SIMP_TAC std_ss [ROR2_THM]
);

val MUST_BE_BIT21 = store_thm("MUST_BE_BIT21",
  `!i. ~(WORD_BIT 24 i /\ ~WORD_BIT 21 i) /\ WORD_BIT 24 i ==> WORD_BIT 21 i`,
  PROVE_TAC []
);

(* -------------------------------------------------------- *)

val ONE_COMPw_THREE_ADD = store_thm("ONE_COMPw_THREE_ADD",
  `!a. a - w32 8 + w32 4 = NOT (w32 3) + a`,
  GEN_REWRITE_TAC (ONCE_DEPTH_CONV o RAND_CONV) empty_rewrites  [WORD_ADD_COMM]
    THEN RW_TAC bool_ss [WORD_NOT,word_1]
    THEN WORD_TAC
    THEN REWRITE_TAC [GSYM WORD_ADD_ASSOC]
    THEN WORD_TAC
);
 
val CPSR_WRITE_READ = store_thm("CPSR_WRITE_READ",
  `(!psr m x. CPSR_READ (SPSR_WRITE psr m x) = CPSR_READ psr) /\
   (!psr x. CPSR_READ (CPSR_WRITE psr x) = x)`,
  RW_TAC bool_ss [CPSR_READ_def,CPSR_WRITE_def,SPSR_WRITE_def,SUBST_def,USER_def,mode2psr_def]
    THEN Cases_on `m`
    THEN FULL_SIMP_TAC bool_ss [mode_case_def,psrs_distinct]
);

val DECODE_MODE_LEM = store_thm("DECODE_MODE_LEM",
  `!m psr. BITS 4 0 (w2n (SET_MODE m psr)) =
                case m of usr -> 16 || fiq -> 17
                       || irq -> 18 || svc -> 19
                       || abt -> 23 || und -> 27 || _ -> 0`,
  Cases THEN RW_TAC arith_ss [w2n_EVAL,SET_MODE_def,MOD_WL_THM,HB_def,BITS_COMP_THM,WORD_SLICE_THM]
    THEN SIMP_TAC std_ss [MOD_TIMES,MOD_EQ_0,SIMP_RULE arith_ss [DIV1] (SPECL [`4`,`0`] BITS_THM2)]
);

val DECODE_MODE_THM = store_thm("DECODE_MODE_THM",
  `!m psr x y. DECODE_MODE (w2n (SET_IFMODE x y m psr)) = m`,
  Cases THEN RW_TAC arith_ss [SET_IFMODE_def,DECODE_MODE_def,DECODE_MODE_LEM]
);
  
val PSR_WRITE_COMM = store_thm("PSR_WRITE_COMM",
  `!psr m x y. SPSR_WRITE (CPSR_WRITE psr x) m y = CPSR_WRITE (SPSR_WRITE psr m y) x`,
  RW_TAC bool_ss [SPSR_WRITE_def,CPSR_WRITE_def,USER_def,mode2psr_def]
    THEN Cases_on `m`
    THEN FULL_SIMP_TAC bool_ss [mode_distinct,mode_case_def,psrs_distinct,SUBST_NE_COMMUTES]
);

(* -------------------------------------------------------- *)
 
val _ = export_theory();
