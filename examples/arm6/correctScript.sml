(* app load ["pairTheory","onestepTheory","word32Theory",
             "armTheory","coreTheory","lemmasTheory","lemmasLib"]; *)
open HolKernel boolLib bossLib Q simpLib PairRules
     arithmeticTheory onestepTheory word32Theory
     armTheory coreTheory lemmasTheory lemmasLib;

(* -------------------------------------------------------- *)

val _ = new_theory "correct";

(* -------------------------------------------------------- *)
(* val _ = Count.counting_thms true; *)
val _ = numLib.prefer_num();
(* -------------------------------------------------------- *)

val lem = prove(
  `!f e. (0 < LET f e) = let x = e in 0 < f x`,
  RW_TAC std_ss [LET_DEF]
);

val DUR_ARM6_WELL = store_thm("DUR_ARM6_WELL",
  `!a. 0 < DUR_ARM6 a`,
  Cases
    THEN Cases_on `d`
    THEN Cases_on `c`
    THEN SIMP_TAC pureSimps.pure_ss [DUR_ARM6_def,lem]
    THEN PBETA_TAC
    THEN SIMP_TAC (pureSimps.pure_ss++numSimps.REDUCE_ss) [ISPEC `$< 0` COND_RAND,COND_ID,lem]
    THEN SIMP_TAC std_ss []
);
 
val IMM_ARM6_THM = store_thm("IMM_ARM6_THM",
  `UIMMERSION IMM_ARM6 STATE_ARM6 DUR_ARM6`,
  RW_TAC bool_ss [UIMMERSION_def,DUR_ARM6_WELL,IMM_ARM6_def]
);

val IMM_ARM6_UNIFORM = store_thm("IMM_ARM6_UNIFORM",
  `UNIFORM IMM_ARM6 STATE_ARM6`,
  REWRITE_TAC [UNIFORM_def]
    THEN EXISTS_TAC `DUR_ARM6`
    THEN REWRITE_TAC [IMM_ARM6_THM]
);

val IMM_ARM6_ONE = MATCH_MP UIMMERSION_ONE (CONJ STATE_ARM6_THM IMM_ARM6_THM);

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val ARM6_DATA_ABSTRACTION = store_thm("ARM6_DATA_ABSTRACTION",
  `DATA_ABSTRACTION ABS_ARM6 (STATE_ARM 0) (STATE_ARM6 0)`,
  RW_TAC bool_ss [DATA_ABSTRACTION_def]
   THEN Cases_on `a`
   THEN EXISTS_TAC `ARM6 f (DP (ADD8_PC f0) f1 a d alua alub) c`
   THEN Cases_on `c`
   THEN SIMP_TAC std_ss [ABS_ARM6_def,SUB8_INV,STATE_ARM_def,STATE_ARM6_def,INIT_ARM6_def]
);

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val ARM6_TCON_LEM0 = store_thm("ARM6_TCON_LEM0",
  `!a. (a = ARM6 mem (DP reg psr areg din alua alub)
               (CTRL pipea pipeaval pipeb pipebval ireg iregval
                  apipea apipeb ointstart onewinst opipebll nxtic nxtis aregn
                  nbw nrw sctrl psrfb oareg)) ==>
   (INIT_ARM6 (STATE_ARM6 (IMM_ARM6 a 0) a) = STATE_ARM6 (IMM_ARM6 a 0) a)`,
   RW_TAC bool_ss []
     THEN SIMP_TAC std_ss [STATE_ARM6_def,IMM_ARM6_def,INIT_ARM6_def,NXTIC_def]
);

val ARM6_TCON_ZERO = GEN_ALL (SIMP_RULE bool_ss [] ARM6_TCON_LEM0);

val ARM6_TCON_LEM1 = Count.apply store_thm("ARM6_TCON_LEM1",
  `!a. (a = ARM6 mem (DP reg psr areg din alua alub)
               (CTRL pipea pipeaval pipeb pipebval ireg iregval
                  apipea apipeb ointstart onewinst opipebll nxtic nxtis aregn
                  nbw nrw sctrl psrfb oareg)) ==>
   (INIT_ARM6 (STATE_ARM6 (IMM_ARM6 a 1) a) = STATE_ARM6 (IMM_ARM6 a 1) a)`,
  RW_TAC bool_ss []
     THEN ABBREV_TAC `a = STATE_ARM6
     (IMM_ARM6
        (ARM6 mem (DP reg psr areg din alua alub)
           (CTRL pipea pipeaval pipeb pipebval ireg iregval
              apipea apipeb ointstart onewinst opipebll nxtic nxtis aregn
              nbw nrw sctrl psrfb oareg)) 1)
     (ARM6 mem (DP reg psr areg din alua alub)
        (CTRL pipea pipeaval pipeb pipebval ireg iregval
           apipea apipeb ointstart onewinst opipebll nxtic nxtis aregn nbw
           nrw sctrl psrfb oareg))`
    THEN POP_ASSUM MP_TAC
    THEN SIMP_TAC std_ss [IMM_ARM6_ONE,INIT_ARM6_def,NXTIC_def]
    THEN ABBREV_TAC `pc = REG_READ6 reg usr 15`
    THEN ABBREV_TAC `i = MEMREAD mem (pc - w32 8)`
    THEN ABBREV_TAC `cpsr = w2n (CPSR_READ psr)`
    THEN Cases_on `~CONDITION_PASSED (BIT 31 cpsr) (BIT 30 cpsr)
                                     (BIT 29 cpsr) (BIT 28 cpsr) (w2n i)`
    THENL [ (* unexecuted *)
      ASM_SIMP_TAC std_ss [iclass_distinct,IC_def,ABORTINST_def,DUR_ARM6_def,DECODE_PSR_def]
        THEN UNFOLD_STATE
        THEN UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE_ss) []
        THEN POP_ASSUM_LIST (K ALL_TAC)
        THEN FINISH_OFF,
         (* executed *)
      FULL_SIMP_TAC bool_ss []
        THEN Cases_on `DECODE_INST (w2n i)`
        THEN ASM_SIMP_TAC std_ss [iclass_distinct,IC_def,ABORTINST_def,DUR_ARM6_def,DECODE_PSR_def]
        THENL [ (* swp *)
           Cases_on `WORD_BITS 15 12 i = 15`
             THEN ASM_SIMP_TAC std_ss [RWA_def,PCCHANGE_def,iseq_distinct,iclass_distinct]
             THEN UNFOLD_STATE
             THEN SWP_ALU3
             THEN SWP_ALU4
             THEN SWP_ALU5
             THEN SWP_ALU6
             THEN NTAC 4 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
             THENL [
               Cases_on `PIPECHANGE (ALUOUT alu4) pc (pc - w32 4)`
                 THEN NTAC 2 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
                 THENL [
                   POP_ASSUM_LIST (K ALL_TAC)
                     THEN FINISH_OFF,
                   RULE_ASSUM_TAC (SIMP_RULE std_ss [PIPECHANGE_def,ALIGN_EQ_def])
                     THEN POP_ASSUM_LIST (fn thl => ASSUME_TAC (hd thl))
                     THEN FINISH_OFF
                 ],
               Cases_on `PIPECHANGE (ALUOUT alu4) pc (pc - w32 4)`
                 THEN ASM_SIMP_TAC std_ss []
                 THENL [
                   PAT_ASSUM `~(x = 15)` (fn th => ASSUME_TAC th)
                     THEN POP_ASSUM_LIST (fn thl => ASSUME_TAC (hd thl))
                     THEN FINISH_OFF,
                   RULE_ASSUM_TAC (SIMP_RULE std_ss [PIPECHANGE_def,ALIGN_EQ_def])
                     THEN FINISH_OFF
                 ]
             ], (* mrs_msr *)
           Cases_on `WORD_BIT 21 i`
             THEN ASM_SIMP_TAC std_ss [RWA_def,PCCHANGE_def,iseq_distinct,iclass_distinct]
             THENL [ (* msr *)
               UNFOLD_STATE
                 THEN UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE_ss) []
                 THEN POP_ASSUM_LIST (K ALL_TAC)
                 THEN FINISH_OFF,
                     (* mrs *)
               Cases_on `WORD_BITS 15 12 i = 15`
                 THEN ASM_SIMP_TAC std_ss []
                 THENL [
                   UNFOLD_STATE
                     THEN MSR_ALU3
                     THEN NTAC 3 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE2_ss) [])
                     THEN POP_ASSUM_LIST (K ALL_TAC)
                     THEN FINISH_OFF,
                   UNFOLD_STATE
                     THEN UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE2_ss) []
                     THEN FINISH_OFF
                 ]
             ],  (* data_proc *)
           Cases_on `WORD_BIT 24 i /\ ~WORD_BIT 23 i`
             THENL [ (* Test or Compare *)
               ASM_SIMP_TAC std_ss [RWA_def,PCCHANGE_def,iseq_distinct,iclass_distinct]
                 THEN UNFOLD_STATE
                 THEN UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE_ss) []
                 THEN POP_ASSUM_LIST (K ALL_TAC)
                 THEN FINISH_OFF,
               RULE_ASSUM_TAC (SIMP_RULE std_ss [])
                 THEN Cases_on `WORD_BITS 15 12 i = 15`
                 THEN ASM_SIMP_TAC std_ss [RWA_def,PCCHANGE_def,iseq_distinct,iclass_distinct]
                 THENL [ (* PCCHANGE *)
                   UNFOLD_STATE
                     THEN DP_ALU3
                     THEN DP_PSR3
                     THEN NTAC 3 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE2_ss) [BUSA_def])
                     THEN POP_ASSUM_LIST (K ALL_TAC)
                     THEN FINISH_OFF,
                         (* NOT PCCHANGE *)
                   UNFOLD_STATE
                     THEN UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE_ss) []
                     THEN FINISH_OFF
                 ]
             ], (* reg_shift *)
           Cases_on `WORD_BIT 24 i /\ ~WORD_BIT 23 i`
             THENL [ (* Test or Compare *)
               ASM_SIMP_TAC std_ss [RWA_def,PCCHANGE_def,iseq_distinct,iclass_distinct]
                 THEN UNFOLD_STATE
                 THEN NTAC 2 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
                 THEN POP_ASSUM_LIST (K ALL_TAC)
                 THEN FINISH_OFF,
               RULE_ASSUM_TAC (SIMP_RULE std_ss [])
                 THEN Cases_on `WORD_BITS 15 12 i = 15`
                 THEN ASM_SIMP_TAC std_ss [RWA_def,PCCHANGE_def,iseq_distinct,iclass_distinct]
                 THENL [ (* PCCHANGE *)
                   UNFOLD_STATE
                     THEN RS_ALU4
                     THEN RS_PSR4
                     THEN NTAC 4 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
                     THEN POP_ASSUM_LIST (K ALL_TAC)
                     THEN FINISH_OFF,
                   UNFOLD_STATE
                     THEN NTAC 2 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
                     THEN FINISH_OFF
                 ]
             ], (* ldr *)
           Cases_on `~WORD_BIT 24 i \/ WORD_BIT 21 i`
             THENL [
               PAT_ASSUM `~a \/ b` (fn th => ASSUME_TAC (REWRITE_RULE [NOT_A_OR_B] th) THEN ASSUME_TAC th)
                 THEN Cases_on `WORD_BITS 19 16 i = 15`
                 THENL [
                   ASM_SIMP_TAC std_ss []
                     THEN UNFOLD_STATE
                     THEN ALU_LDR4
                     THEN NTAC 5 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
                     THEN POP_ASSUM_LIST (K ALL_TAC)
                     THEN FINISH_OFF,
                   Cases_on `WORD_BITS 15 12 i = 15`
                     THEN ASM_SIMP_TAC std_ss []
                     THEN UNFOLD_STATE
                     THEN ALU_LDR3
                     THEN ALU_LDR4
                     THEN ALU_LDR5
                     THEN NTAC 3 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
                     THENL [
                       NTAC 2 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
                         THEN POP_ASSUM_LIST (K ALL_TAC)
                         THEN FINISH_OFF,
                       NTAC 3 (POP_ASSUM (K ALL_TAC))
                         THEN FINISH_OFF
                     ]
                 ],
               PAT_ASSUM `~(~a \/ b)` (fn th => ASSUME_TAC (REWRITE_RULE [NOT_A_OR_B] th) THEN ASSUME_TAC th)
                 THEN Cases_on `WORD_BITS 15 12 i = 15`
                 THEN ASM_SIMP_TAC std_ss []
                 THEN UNFOLD_STATE
                 THEN ALU_LDR3
                 THEN ALU_LDR4
                 THEN ALU_LDR5
                 THEN NTAC 3 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
                 THENL [
                   NTAC 2 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
                     THEN POP_ASSUM_LIST (K ALL_TAC)
                     THEN FINISH_OFF,
                   NTAC 3 (POP_ASSUM (K ALL_TAC))
                     THEN FINISH_OFF
                 ]
             ], (* str *)
           Cases_on `~WORD_BIT 24 i \/ WORD_BIT 21 i`
             THENL [
               PAT_ASSUM `~a \/ b` (fn th => ASSUME_TAC (REWRITE_RULE [NOT_A_OR_B] th) THEN ASSUME_TAC th)
                 THEN Cases_on `WORD_BITS 19 16 i = 15`
                 THEN ASM_SIMP_TAC std_ss []
                 THEN UNFOLD_STATE
                 THEN ALU_STR3
                 THEN ALU_STR4
                 THEN NTAC 2 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
                 THENL [
                   NTAC 2 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
                     THEN POP_ASSUM_LIST (K ALL_TAC)
                     THEN FINISH_OFF,
                   SIMP_TAC std_ss [PIPECHANGE_def,ALIGN_EQ_def]
                     THEN PAT_ASSUM `~(x = 15)` (fn th => ASSUME_TAC th)
                     THEN POP_ASSUM_LIST (fn thl => ASSUME_TAC (hd thl))
                     THEN FINISH_OFF
                 ],
               ASM_SIMP_TAC std_ss []
                 THEN PAT_ASSUM `~(~a \/ b)` (fn th => ASSUME_TAC (REWRITE_RULE [NOT_A_OR_B] th) THEN ASSUME_TAC th)
                 THEN UNFOLD_STATE
                 THEN ALU_STR3
                 THEN NTAC 2 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
                 THEN SIMP_TAC std_ss [PIPECHANGE_def,ALIGN_EQ_def]
                 THEN POP_ASSUM_LIST (K ALL_TAC)
                 THEN FINISH_OFF
             ],  (* br *)
           UNFOLD_STATE
             THEN UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) []
             THEN ALU_BR3
             THEN ALU_BR4
             THEN ALU_BR5
             THEN Cases_on `WORD_BIT 24 i`
             THEN NTAC 2 (UNFOLD_NEXT THEN ASM_SIMP_TAC (arith_ss++CORE3_ss) [])
             THEN POP_ASSUM_LIST (K ALL_TAC)
             THEN FINISH_OFF2,
             (* swi_ex *)
           UNFOLD_STATE
             THEN ALU_SWI3
             THEN PSR_SWI3
             THEN ALU_SWI4
             THEN PSR_SWI4
             THEN NTAC 3 (UNFOLD_NEXT THEN ASM_SIMP_TAC (arith_ss++CORE3_ss) [])
             THEN POP_ASSUM_LIST (K ALL_TAC)
             THEN FINISH_OFF2,
             (* undef *)
           UNFOLD_STATE
             THEN ALU_UNDEF3
             THEN PSR_UNDEF3
             THEN ALU_UNDEF4
             THEN PSR_UNDEF4
             THEN NTAC 4 (UNFOLD_NEXT THEN ASM_SIMP_TAC (arith_ss++CORE3_ss) [])
             THEN POP_ASSUM_LIST (K ALL_TAC)
             THEN FINISH_OFF2,
           FULL_SIMP_TAC bool_ss [DECODE_INST_NOT_UNEXEC]
        ]
    ]
);
 
val ARM6_TCON_ONE = GEN_ALL (SIMP_RULE bool_ss [] ARM6_TCON_LEM1);

val INIT = REWRITE_RULE [GSYM FUN_EQ_THM] (CONJUNCT1 STATE_ARM6_def);

val ARM6_TIME_CON_IMM = store_thm("ARM6_TIME_CON_IMM",
  `TCON_IMMERSION STATE_ARM6 IMM_ARM6`,
  SIMP_TAC bool_ss [TC_IMMERSION_ONE_STEP_THM,STATE_ARM6_IMAP,IMM_ARM6_UNIFORM]
    THEN REPEAT STRIP_TAC
    THEN MAP_EVERY Cases_on [`a`,`d`,`c`]
    THEN REWRITE_TAC [INIT,ARM6_TCON_ZERO,ARM6_TCON_ONE]
);

(* -------------------------------------------------------- *)

val BIT_W32_NUM = GSYM WORD_BIT_def;
val BITS_W32_NUM = GSYM WORD_BITS_def;

val ARM6_COR_LEM0 = store_thm("ARM6_COR_LEM0",
  `!a. (a = ARM6 mem (DP reg psr areg din alua alub)
               (CTRL pipea pipeaval pipeb pipebval ireg iregval
                  apipea apipeb ointstart onewinst opipebll nxtic nxtis aregn
                  nbw nrw sctrl psrfb oareg)) ==>
   (STATE_ARM 0 (ABS_ARM6 a) = ABS_ARM6 (STATE_ARM6 (IMM_ARM6 a 0) a))`,
  RW_TAC bool_ss []
    THEN SIMP_TAC std_ss [STATE_ARM6_def,IMM_ARM6_def,INIT_ARM6_def,ABS_ARM6_def,STATE_ARM_def]
);

val ARM6_COR_ZERO = GEN_ALL (SIMP_RULE bool_ss [] ARM6_COR_LEM0);

val ARM6_COR_LEM1 = Count.apply store_thm("ARM6_COR_LEM1",
  `!a. (a = ARM6 mem (DP reg psr areg din alua alub)
               (CTRL pipea pipeaval pipeb pipebval ireg iregval
                  apipea apipeb ointstart onewinst opipebll nxtic nxtis aregn
                  nbw nrw sctrl psrfb oareg)) ==>
   (STATE_ARM 1 (ABS_ARM6 a) = ABS_ARM6 (STATE_ARM6 (IMM_ARM6 a 1) a))`,
  RW_TAC bool_ss []
    THEN SIMP_TAC std_ss [IMM_ARM6_ONE,INIT_ARM6_def,NXTIC_def]
    THEN ABBREV_TAC `pc = REG_READ6 reg usr 15`
    THEN ABBREV_TAC `i = MEMREAD mem (pc - w32 8)`
    THEN ABBREV_TAC `cpsr = w2n (CPSR_READ psr)`
    THEN SIMP_TAC bool_ss [ABS_ARM6_def]
    THEN UNFOLD_SPEC
    THEN Cases_on `~CONDITION_PASSED (BIT 31 cpsr) (BIT 30 cpsr)
                                     (BIT 29 cpsr) (BIT 28 cpsr) (w2n i)`
    THENL [ (* unexecuted *)
      ASM_SIMP_TAC std_ss [iclass_distinct,IC_def,ABORTINST_def,DUR_ARM6_def,DECODE_PSR_def]
        THEN UNFOLD_STATE
        THEN UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE_ss) [BUSA_def,BUSB_def,PSRWA_def]
        THEN ASM_SIMP_TAC std_ss [ABS_ARM6_def,NEXT_ARM_def,DECODE_PSR_def,FETCH_SUB8,BITS_W32_NUM]
        THEN RW_TAC std_ss [NOOP_REG],
      FULL_SIMP_TAC bool_ss []
        THEN Cases_on `DECODE_INST (w2n i)`
        THEN ASM_SIMP_TAC std_ss [iclass_distinct,IC_def,ABORTINST_def,DUR_ARM6_def,DECODE_PSR_def]
        THENL [ (* swp *)
           Cases_on `WORD_BITS 15 12 i = 15`
             THEN ASM_SIMP_TAC std_ss [RWA_def,PCCHANGE_def,iseq_distinct,iclass_distinct]
             THEN UNFOLD_STATE
             THEN SWP_ALU3
             THEN SWP_ALU4
             THEN SWP_ALU5
             THEN SWP_ALU6
             THEN NTAC 4 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
             THENL [
               NTAC 2 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
                 THEN ASM_SIMP_TAC std_ss [ABS_ARM6_def,NEXT_ARM_def,DECODE_PSR_def,FETCH_SUB8,BITS_W32_NUM,iclass_distinct]
                 THEN ABBREV_TAC `alu3' = ALUOUT alu3`
                 THEN PAT_ASSUM `x = alu3` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM th]))
                 THEN ABBREV_TAC `alu4' = ALUOUT alu4`
                 THEN PAT_ASSUM `x = alu4` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM th]))
                 THEN PAT_ASSUM `x = alu5` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM th]))
                 THEN ABBREV_TAC `alu6' = ALUOUT alu6`
                 THEN PAT_ASSUM `x = alu6` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM th]))
                 THEN RULE_ASSUM_TAC (SIMP_RULE std_ss [SWP_ALU6_T,RBA_def,SHIFTER_def,LSL_ZERO,SWP_SHIFT,
                                                        iseq_distinct,iclass_distinct])
                 THEN NTAC 3 (POP_ASSUM (fn th => REWRITE_TAC [SYM th]))
                 THEN Cases_on `PIPECHANGE (REG_READ6 reg (DECODE_MODE cpsr) (WORD_BITS 19 16 i))
                                           pc (pc - w32 4)`
                 THEN ASM_SIMP_TAC std_ss []
                 THEN RULE_ASSUM_TAC (SIMP_RULE std_ss [PIPECHANGE_def,ALIGN_EQ_def])
                 THEN RULE_ASSUM_TAC (ONCE_REWRITE_RULE [DISJ_COMM])
                 THEN ASM_SIMP_TAC std_ss [BIT_W32_NUM,BITS_W32_NUM,SWP_def,DECODE_SWP_def]
                 THEN SIMP_TAC std_ss [REG_READ_SUB8_PC,FETCH_SUB8,GSYM WORD_ADD_SUB_SYM,ADD4_SUB8_THM,
                                       REGISTER_RANGES,WORD_ADD_SUB,PIPE_OKAY_def]
                 THEN ONCE_REWRITE_TAC [GSYM DE_MORGAN_THM]
                 THEN ASM_REWRITE_TAC []
                 THEN UNABBREV_TAC `pc`
                 THEN POP_ASSUM_LIST (fn thl => ASSUME_TAC (hd thl))
                 THEN RW_TAC std_ss [INC_PC_READ,SLICE_ROR_THM,FIELD_def,OP_REG,RBA_def,REGISTER_RANGES,
                                     MEM_READ_def,MEM_READ_BYTE_def,MEM_READ_WORD_def,MEMREAD_def],
               ASM_SIMP_TAC std_ss [ABS_ARM6_def,NEXT_ARM_def,DECODE_PSR_def,FETCH_SUB8,BITS_W32_NUM,
                                    REG_WRITE_COMMUTES,REGISTER_RANGES,iclass_distinct]
                 THEN ABBREV_TAC `alu3' = ALUOUT alu3`
                 THEN PAT_ASSUM `x = alu3` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM th]))
                 THEN ABBREV_TAC `alu4' = ALUOUT alu4`
                 THEN PAT_ASSUM `x = alu4` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM th]))
                 THEN PAT_ASSUM `x = alu5` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM th]))
                 THEN ABBREV_TAC `alu6' = ALUOUT alu6`
                 THEN PAT_ASSUM `x = alu6` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM th]))
                 THEN RULE_ASSUM_TAC (SIMP_RULE std_ss [SWP_ALU6_T,RBA_def,SHIFTER_def,LSL_ZERO,SWP_SHIFT,
                                                        iseq_distinct,iclass_distinct])
                 THEN NTAC 3 (POP_ASSUM (fn th => REWRITE_TAC [SYM th]))
                 THEN Cases_on `PIPECHANGE (REG_READ6 reg (DECODE_MODE cpsr) (WORD_BITS 19 16 i))
                                           pc (pc - w32 4)`
                 THEN ASM_SIMP_TAC std_ss []
                 THEN RULE_ASSUM_TAC (SIMP_RULE std_ss [PIPECHANGE_def,ALIGN_EQ_def])
                 THEN RULE_ASSUM_TAC (ONCE_REWRITE_RULE [DISJ_COMM])
                 THEN ASM_SIMP_TAC std_ss [BIT_W32_NUM,BITS_W32_NUM,SWP_def,DECODE_SWP_def]
                 THEN SIMP_TAC std_ss [REG_READ_SUB8_PC,FETCH_SUB8,GSYM WORD_ADD_SUB_SYM,ADD4_SUB8_THM,
                                       REGISTER_RANGES,WORD_ADD_SUB,PIPE_OKAY_def]
                 THEN ONCE_REWRITE_TAC [GSYM DE_MORGAN_THM]
                 THEN ASM_REWRITE_TAC []
                 THEN UNABBREV_TAC `pc`
                 THEN PAT_ASSUM `~(x = 15)` (fn th => ASSUME_TAC th)
                 THEN POP_ASSUM_LIST (fn thl => ASSUME_TAC (CONJ (hd thl) (hd (tl thl))))
                 THEN RW_TAC std_ss [INC_PC_READ,SLICE_ROR_THM,FIELD_def,OP_INC_REG,RBA_def,REGISTER_RANGES,
                                     MEM_READ_def,MEM_READ_BYTE_def,MEM_READ_WORD_def,MEMREAD_def]
             ], (* mrs_msr *)
           Cases_on `WORD_BIT 21 i`
             THEN ASM_SIMP_TAC std_ss [RWA_def,PCCHANGE_def,iseq_distinct,iclass_distinct]
             THENL [ (* msr *)
               UNFOLD_STATE
                 THEN UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE_ss) []
                 THEN ASM_SIMP_TAC std_ss [ABS_ARM6_def,NEXT_ARM_def,DECODE_PSR_def,FETCH_SUB8,BITS_W32_NUM]
                 THEN ASM_SIMP_TAC std_ss [BIT_W32_NUM,BITS_W32_NUM,MSR_def,DECODE_MSR_def,MSR_ALU,SPLIT_WORD_def,
                                           ALUAWRITE_def,ALUBWRITE_def,PSRFBWRITE_def,BUSA_def,BUSB_def,
                                           FIELD_def,RBA_def,iseq_distinct,iclass_distinct]
                 THEN Cases_on `USER (DECODE_MODE cpsr)`
                 THEN Cases_on `WORD_BIT 22 i`
                 THEN Cases_on `WORD_BIT 19 i`
                 THEN Cases_on `WORD_BIT 16 i`
                 THEN ASM_SIMP_TAC std_ss [PSRDAT_def,BIT_W32_NUM,BITS_W32_NUM,MSR_def,DECODE_MSR_def,
                                           PSRA_def,PSRWA_def,ALUOUT_ALU_logic,iclass_distinct,iseq_distinct]
                 THEN UNABBREV_TAC `pc`
                 THEN POP_ASSUM_LIST (K ALL_TAC)
                 THEN RW_TAC std_ss [NOOP_REG,GSYM WORD_SLICE_THM,CONCAT_BYTES_def,IMMEDIATE_THM,SHIFTER_def,
                                     WORD_BITS118_LEM,GSYM ADD_ASSOC,bitsTheory.TIMES_2EXP_def,WORD_SLICE_COMP_MSR1,
                                     REG_READ_SUB8_PC,ROR2_THM2,LSL_ZERO,REGISTER_RANGES]
                 THEN SIMP_TAC arith_ss [GSYM WORD_SLICE_ZERO_THM,WORD_SLICE_COMP_MSR2],
                     (* mrs *)
               Cases_on `WORD_BITS 15 12 i = 15`
                 THEN ASM_SIMP_TAC std_ss []
                 THENL [
                   UNFOLD_STATE
                     THEN MSR_ALU3
                     THEN NTAC 3 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE2_ss) [])
                     THEN ASM_SIMP_TAC std_ss [ABS_ARM6_def,NEXT_ARM_def,DECODE_PSR_def,FETCH_SUB8,BITS_W32_NUM,
                                               REG_WRITE_COMMUTES,REGISTER_RANGES,REG_WRITE_WRITE_PC]
                     THEN POP_ASSUM (fn th => REWRITE_TAC [SYM th])
                     THEN ASM_SIMP_TAC std_ss [BIT_W32_NUM,BITS_W32_NUM,MRS_def,DECODE_MRS_def,MRS_ALU,
                                          PSRA_def,ALUAWRITE_def,ALUBWRITE_def,PSRFBWRITE_def,BUSA_def,BUSB_def,
                                          FIELD_def,RBA_def,ALUOUT_ALU_logic,iseq_distinct,iclass_distinct]
                     THEN SIMP_TAC std_ss [IF_NEG,OP_REG],
                   UNFOLD_STATE
                     THEN UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE2_ss) []
                     THEN ASM_SIMP_TAC std_ss [ABS_ARM6_def,NEXT_ARM_def,DECODE_PSR_def,FETCH_SUB8,BITS_W32_NUM,
                                              REG_WRITE_COMMUTES,REGISTER_RANGES,REG_WRITE_WRITE_PC]
                     THEN ASM_SIMP_TAC std_ss [BIT_W32_NUM,BITS_W32_NUM,MRS_def,DECODE_MRS_def,MRS_ALU,
                                          PSRA_def,ALUAWRITE_def,ALUBWRITE_def,PSRFBWRITE_def,
                                          BUSA_def,BUSB_def,OP_INC_REG,REGISTER_RANGES,
                                          FIELD_def,RBA_def,ALUOUT_ALU_logic,iseq_distinct,iclass_distinct,IF_NEG,OP_REG]
                 ]
             ],  (* data_proc *)
           Cases_on `WORD_BIT 24 i /\ ~WORD_BIT 23 i`
             THENL [ (* Test or Compare *)
               ASM_SIMP_TAC std_ss [RWA_def,PCCHANGE_def,iseq_distinct,iclass_distinct]
                 THEN UNFOLD_STATE
                 THEN UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE_ss) []
                 THEN ASM_SIMP_TAC std_ss [ABS_ARM6_def,NEXT_ARM_def,DECODE_PSR_def,FETCH_SUB8,BITS_W32_NUM]
                 THEN ASM_SIMP_TAC std_ss [BIT_W32_NUM,BITS_W32_NUM,DATA_PROCESSING_def,DECODE_DATAP_def,
                                           PSRWA_def,ALU6_def,TEST_OR_COMP_THM3,ADDR_MODE1_def,
                                           ALUAWRITE_def,ALUBWRITE_def,PSRFBWRITE_def,BUSA_def,BUSB_def,
                                           FIELD_def,RBA_def,iseq_distinct,iclass_distinct]
                 THEN Cases_on `WORD_BIT 20 i`
                 THENL [
                   Cases_on `WORD_BITS 15 12 i = 15`
                     THEN ASM_SIMP_TAC std_ss [PSRDAT_def,PSRA_def,SPSR_READ_THM,
                                               iseq_distinct,iclass_distinct]
                     THENL [
                       REWRITE_TAC [LET_THM]
                         THEN PBETA_TAC
                         THEN RW_TAC std_ss [NOOP_REG],
                       Cases_on `WORD_BIT 25 i`
                         THEN IMP_RES_TAC DATA_PROC_IMP_NOT_BIT4
                         THEN ASM_SIMP_TAC std_ss [ARITHMETIC_THM2,RAA_def,WORD_BITS118_LEM,SHIFTER_def,IMMEDIATE_THM,
                                                   SHIFT_IMMEDIATE_THM2,iseq_distinct,iclass_distinct]
                         THEN UNABBREV_TAC `pc`
                         THEN POP_ASSUM_LIST (K ALL_TAC)
                         THEN REWRITE_TAC [LET_THM]
                         THEN PBETA_TAC
                         THEN RW_TAC std_ss [NOOP_REG,REG_READ_SUB8_PC,NZCV_ALUOUT_THM,REGISTER_RANGES]
                         THEN FULL_SIMP_TAC std_ss []
                     ],
                   ASM_SIMP_TAC std_ss [PSRDAT_def,PSRA_def,SPSR_READ_THM,
                                        iseq_distinct,iclass_distinct]
                     THEN REWRITE_TAC [LET_THM]
                     THEN PBETA_TAC
                     THEN RW_TAC std_ss [NOOP_REG]
                 ],
               PAT_ASSUM `~(a /\ ~b)` (fn th => ASSUME_TAC (REWRITE_RULE [GSYM NOT_A_OR_B] th) THEN ASSUME_TAC th)
                 THEN Cases_on `WORD_BITS 15 12 i = 15`
                 THEN ASM_SIMP_TAC std_ss [RWA_def,PCCHANGE_def,iseq_distinct,iclass_distinct]
                 THENL [ (* PCCHANGE *)
                   UNFOLD_STATE
                     THEN DP_ALU3
                     THEN DP_PSR3
                     THEN NTAC 3 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE2_ss) [BUSA_def])
                     THEN ASM_SIMP_TAC std_ss [ABS_ARM6_def,NEXT_ARM_def,DECODE_PSR_def,FETCH_SUB8,BITS_W32_NUM,iclass_distinct]
                     THEN POP_ASSUM (fn th => REWRITE_TAC [SYM th])
                     THEN POP_ASSUM (fn th => REWRITE_TAC [SYM th])
                     THEN ASM_SIMP_TAC std_ss [BIT_W32_NUM,BITS_W32_NUM,DATA_PROCESSING_def,
                                           DECODE_DATAP_def,PSRWA_def,ALU6_def,TEST_OR_COMP_THM3,ADDR_MODE1_def,
                                           ALUAWRITE_def,ALUBWRITE_def,PSRFBWRITE_def,BUSA_def,BUSB_def,
                                           FIELD_def,RBA_def,iseq_distinct,iclass_distinct]
                     THEN Cases_on `WORD_BIT 20 i`
                     THEN ASM_SIMP_TAC std_ss [PSRDAT_def,PSRA_def,SPSR_READ_THM,
                                            WORD_BITS118_LEM,SHIFTER_def,iseq_distinct,iclass_distinct]
                     THEN Cases_on `WORD_BIT 25 i`
                     THEN IMP_RES_TAC DATA_PROC_IMP_NOT_BIT4
                     THEN ASM_SIMP_TAC std_ss [RAA_def,IMMEDIATE_THM,SHIFT_IMMEDIATE_THM2,iseq_distinct,iclass_distinct]
                     THEN POP_ASSUM_LIST (K ALL_TAC)
                     THEN REWRITE_TAC [LET_THM]
                     THEN PBETA_TAC
                     THEN RW_TAC std_ss [OP_REG,REG_READ_SUB8_PC,NZCV_ALUOUT_THM,PC_WRITE_MODE_FREE,REGISTER_RANGES],
                         (* NOT PCCHANGE *)
                   UNFOLD_STATE
                     THEN UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE_ss) []
                     THEN ASM_SIMP_TAC std_ss [ABS_ARM6_def,NEXT_ARM_def,DECODE_PSR_def,FETCH_SUB8,BITS_W32_NUM,
                                               REG_WRITE_COMMUTES,REGISTER_RANGES,REG_WRITE_WRITE_PC,iclass_distinct]
                     THEN ASM_SIMP_TAC std_ss [BIT_W32_NUM,BITS_W32_NUM,DATA_PROCESSING_def,
                                           DECODE_DATAP_def,PSRWA_def,ALU6_def,TEST_OR_COMP_THM3,ADDR_MODE1_def,
                                           ALUAWRITE_def,ALUBWRITE_def,PSRFBWRITE_def,BUSA_def,BUSB_def,
                                           FIELD_def,RBA_def,iseq_distinct,iclass_distinct]
                     THEN Cases_on `WORD_BIT 20 i`
                     THEN ASM_SIMP_TAC std_ss [PSRDAT_def,PSRA_def,SPSR_READ_THM,
                                            WORD_BITS118_LEM,SHIFTER_def,iseq_distinct,iclass_distinct]
                     THEN Cases_on `WORD_BIT 25 i`
                     THEN IMP_RES_TAC DATA_PROC_IMP_NOT_BIT4
                     THEN ASM_SIMP_TAC std_ss [ARITHMETIC_THM2,RAA_def,IMMEDIATE_THM,SHIFT_IMMEDIATE_THM2,
                                               iseq_distinct,iclass_distinct]
                     THEN ONCE_REWRITE_TAC [DISJ_TO_CONJ]
                     THEN REWRITE_TAC [IF_NEG]
                     THEN REWRITE_TAC [LET_THM]
                     THEN PBETA_TAC
                     THEN RW_TAC std_ss [OP_INC_REG,REG_READ_SUB8_PC,NZCV_ALUOUT_THM,REGISTER_RANGES]
                 ]
             ], (* reg_shift *)
           IMP_RES_TAC REG_SHIFT_IMP_BITS
             THEN Cases_on `WORD_BIT 24 i /\ ~WORD_BIT 23 i`
             THENL [ (* Test or Compare *)
               ASM_SIMP_TAC std_ss [RWA_def,PCCHANGE_def,iseq_distinct,iclass_distinct]
                 THEN UNFOLD_STATE
                 THEN NTAC 2 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
                 THEN ASM_SIMP_TAC std_ss [ABS_ARM6_def,NEXT_ARM_def,DECODE_PSR_def,FETCH_SUB8,BITS_W32_NUM]
                 THEN ASM_SIMP_TAC std_ss [BIT_W32_NUM,BITS_W32_NUM,DATA_PROCESSING_def,DECODE_DATAP_def,
                                           PSRWA_def,ALU6_def,TEST_OR_COMP_THM3,ADDR_MODE1_def,
                                           ALUAWRITE_def,ALUBWRITE_def,PSRFBWRITE_def,BUSA_def,BUSB_def,
                                           FIELD_def,RBA_def,iseq_distinct,iclass_distinct]
                 THEN Cases_on `WORD_BIT 20 i`
                 THENL [
                   Cases_on `WORD_BITS 15 12 i = 15`
                     THEN ASM_SIMP_TAC std_ss [PSRDAT_def,PSRA_def,SPSR_READ_THM,
                                               iseq_distinct,iclass_distinct]
                     THENL [
                       REWRITE_TAC [LET_THM]
                         THEN PBETA_TAC
                         THEN RW_TAC std_ss [NOOP_REG],
                       ASM_SIMP_TAC std_ss [ARITHMETIC_THM2,RAA_def,WORD_BITS118_LEM,SHIFTER_def,
                                            SHIFT_REGISTER_THM2,iseq_distinct,iclass_distinct]
                         THEN UNABBREV_TAC `pc`
                         THEN POP_ASSUM_LIST (K ALL_TAC)
                         THEN REWRITE_TAC [LET_THM,IF_NEG]
                         THEN PBETA_TAC
                         THEN RW_TAC std_ss [INC_PC_READ,NOOP_REG,REG_READ_SUB8_PC,NZCV_ALUOUT_THM,REGISTER_RANGES]
                     ],
                   ASM_SIMP_TAC std_ss [PSRDAT_def,PSRA_def,SPSR_READ_THM,
                                        iseq_distinct,iclass_distinct]
                     THEN REWRITE_TAC [LET_THM]
                     THEN PBETA_TAC
                     THEN RW_TAC std_ss [NOOP_REG]
                 ],
               PAT_ASSUM `~(a /\ ~b)` (fn th => ASSUME_TAC (REWRITE_RULE [GSYM NOT_A_OR_B] th) THEN ASSUME_TAC th)
                 THEN Cases_on `WORD_BITS 15 12 i = 15`
                 THEN ASM_SIMP_TAC std_ss [RWA_def,PCCHANGE_def,iseq_distinct,iclass_distinct]
                 THENL [ (* PCCHANGE *)
                   UNFOLD_STATE
                     THEN RS_ALU4
                     THEN RS_PSR4
                     THEN NTAC 4 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
                     THEN ASM_SIMP_TAC std_ss [ABS_ARM6_def,NEXT_ARM_def,DECODE_PSR_def,FETCH_SUB8,BITS_W32_NUM,iclass_distinct]
                     THEN POP_ASSUM (fn th => REWRITE_TAC [SYM th])
                     THEN POP_ASSUM (fn th => REWRITE_TAC [SYM th])
                     THEN ASM_SIMP_TAC std_ss [BIT_W32_NUM,BITS_W32_NUM,DATA_PROCESSING_def,
                                           DECODE_DATAP_def,PSRWA_def,ALU6_def,TEST_OR_COMP_THM3,ADDR_MODE1_def,
                                           ALUAWRITE_def,ALUBWRITE_def,PSRFBWRITE_def,BUSA_def,BUSB_def,
                                           FIELD_def,RBA_def,iseq_distinct,iclass_distinct]
                     THEN Cases_on `WORD_BIT 20 i`
                     THEN ASM_SIMP_TAC std_ss [PSRDAT_def,PSRA_def,SPSR_READ_THM,
                                               WORD_BITS118_LEM,SHIFTER_def,RAA_def,SHIFT_REGISTER_THM2,
                                               iseq_distinct,iclass_distinct]
                     THEN UNABBREV_TAC `pc`
                     THEN POP_ASSUM_LIST (K ALL_TAC)
                     THEN REWRITE_TAC [LET_THM]
                     THEN PBETA_TAC
                     THEN RW_TAC std_ss [INC_PC_READ,OP_REG,REG_READ_SUB8_PC,NZCV_ALUOUT_THM,PC_WRITE_MODE_FREE,REGISTER_RANGES],
                   UNFOLD_STATE
                     THEN NTAC 2 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
                     THEN ASM_SIMP_TAC std_ss [ABS_ARM6_def,NEXT_ARM_def,DECODE_PSR_def,FETCH_SUB8,BITS_W32_NUM,
                                               REG_WRITE_WRITE_PC,REG_WRITE_COMMUTES,REGISTER_RANGES,iclass_distinct]
                     THEN ASM_SIMP_TAC std_ss [BIT_W32_NUM,BITS_W32_NUM,DATA_PROCESSING_def,
                                           DECODE_DATAP_def,PSRWA_def,ALU6_def,TEST_OR_COMP_THM3,ADDR_MODE1_def,
                                           ALUAWRITE_def,ALUBWRITE_def,PSRFBWRITE_def,BUSA_def,BUSB_def,
                                           FIELD_def,RBA_def,iseq_distinct,iclass_distinct]
                     THEN Cases_on `WORD_BIT 20 i`
                     THEN ASM_SIMP_TAC std_ss [PSRDAT_def,PSRA_def,SPSR_READ_THM,
                                               WORD_BITS118_LEM,SHIFTER_def,ARITHMETIC_THM2,RAA_def,SHIFT_REGISTER_THM2,
                                               iseq_distinct,iclass_distinct]
                     THEN ONCE_REWRITE_TAC [DISJ_TO_CONJ]
                     THEN REWRITE_TAC [IF_NEG]
                     THEN REWRITE_TAC [LET_THM]
                     THEN PBETA_TAC
                     THEN RW_TAC std_ss [OP_INC_REG,INC_PC_READ,REG_READ_SUB8_PC,NZCV_ALUOUT_THM,REGISTER_RANGES]
                 ]
             ], (* ldr *)
           IMP_RES_TAC LDR_IMP_BITS
             THEN Cases_on `~WORD_BIT 24 i \/ WORD_BIT 21 i`
             THENL [
               Cases_on `WORD_BITS 19 16 i = 15`
                 THENL [
                   ASM_SIMP_TAC std_ss []
                     THEN UNFOLD_STATE
                     THEN PAT_ASSUM `~a \/ b` (fn th => ASSUME_TAC (REWRITE_RULE [NOT_A_OR_B] th) THEN ASSUME_TAC th
                                                          THEN ASSUME_TAC (ONCE_REWRITE_RULE [DISJ_SYM] th))
                     THEN ALU_LDR4
                     THEN NTAC 5 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
                     THEN ASM_SIMP_TAC std_ss [ABS_ARM6_def,NEXT_ARM_def,DECODE_PSR_def,
                                               FETCH_SUB8,BITS_W32_NUM,iclass_distinct]
                     THEN POP_ASSUM (fn th => REWRITE_TAC [SYM th])
                     THEN ASM_SIMP_TAC std_ss [BIT_W32_NUM,BITS_W32_NUM,LDR_STR_def,RAA_def,SHIFT_IMMEDIATE_THM2,
                                           BIT2_OPC,DECODE_LDR_STR_def,ALU6_def,ADDR_MODE2_def,
                                           SHIFTER_def,FIELD_def,RBA_def,iseq_distinct,iclass_distinct]
                     THEN Cases_on `WORD_BIT 23 i`  (* UP/DOWN *)
                     THEN ASM_SIMP_TAC std_ss [IF_NEG,UP_DOWN_def,ALUOUT_ADD,ALUOUT_SUB]
                     THEN POP_ASSUM_LIST (K ALL_TAC)
                     THEN RW_TAC std_ss [INC_PC_READ,INC_WB_REG,OP_REG,REG_READ_SUB8_PC,LSL_ZERO,REGISTER_RANGES],
                   PAT_ASSUM `~a \/ b` (fn th => ASSUME_TAC (REWRITE_RULE [NOT_A_OR_B] th) THEN ASSUME_TAC th)
                     THEN Cases_on `WORD_BITS 15 12 i = 15`
                     THEN ASM_SIMP_TAC std_ss []
                     THEN UNFOLD_STATE
                     THEN ALU_LDR3
                     THEN ALU_LDR4
                     THEN ALU_LDR5
                     THEN NTAC 3 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
                     THENL [
                       NTAC 2 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
                         THEN ASM_SIMP_TAC std_ss [ABS_ARM6_def,NEXT_ARM_def,DECODE_PSR_def,REG_WRITE_WRITE_PC,
                                                   REG_WRITE_COMMUTES,REGISTER_RANGES,FETCH_SUB8,BITS_W32_NUM,iclass_distinct]
                         THEN ABBREV_TAC `alu3' = ALUOUT alu3`
                         THEN PAT_ASSUM `x = alu3` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM th]))
                         THEN ABBREV_TAC `alu4' = ALUOUT alu4`
                         THEN PAT_ASSUM `x = alu4` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM th]))
                         THEN ABBREV_TAC `alu5' = ALUOUT alu5`
                         THEN PAT_ASSUM `x = alu5` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM th]))
                         THEN NTAC 3 (POP_ASSUM MP_TAC)
                         THEN Cases_on `WORD_BIT 25 i`  (* IMMEDIATE *)
                         THEN ASM_SIMP_TAC std_ss [iseq_distinct,iclass_distinct,RAA_def,RBA_def,
                                                   LDR_ALU6_T5,LDR_SHIFT_REG_T3,LDR_SHIFT_IMM_T3,LDR_FIELD_T3]
                         THEN Cases_on `WORD_BIT 23 i`  (* UP/DOWN *)
                         THEN Cases_on `WORD_BIT 24 i`  (* PRE/POST *)
                         THEN IMP_RES_TAC MUST_BE_BIT21
                         THEN ASM_SIMP_TAC std_ss [iseq_distinct,iclass_distinct,BIT2_OPC,BIT3_OPC,ALU6_def,
                                                   ALUOUT_ALU_logic,ALUOUT_ADD,ALUOUT_SUB,UP_DOWN_def,
                                                   REGISTER_RANGES,REG_READ_SUB8_PC,
                                                   BIT_W32_NUM,BITS_W32_NUM,LDR_STR_def,SHIFT_IMMEDIATE_THM2,
                                                   SHIFTER_def,ADDR_MODE2_def,DECODE_LDR_STR_def]
                         THEN POP_ASSUM_LIST (K ALL_TAC)
                         THEN REPEAT (STRIP_GOAL_THEN (fn th => REWRITE_TAC [SYM th]))
                         THEN RW_TAC std_ss [SLICE_ROR_THM,FIELD_def,OP_REG2,SWP_SHIFT,REGISTER_RANGES,
                                             MEM_READ_def,MEM_READ_BYTE_def,MEMREAD_def,MEM_READ_WORD_def],
                       ASM_SIMP_TAC std_ss [ABS_ARM6_def,NEXT_ARM_def,DECODE_PSR_def,REG_WRITE_WRITE_PC,
                                                   REG_WRITE_COMMUTES,REGISTER_RANGES,FETCH_SUB8,BITS_W32_NUM,iclass_distinct]
                         THEN ABBREV_TAC `alu3' = ALUOUT alu3`
                         THEN PAT_ASSUM `x = alu3` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM th]))
                         THEN ABBREV_TAC `alu4' = ALUOUT alu4`
                         THEN PAT_ASSUM `x = alu4` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM th]))
                         THEN ABBREV_TAC `alu5' = ALUOUT alu5`
                         THEN PAT_ASSUM `x = alu5` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM th]))
                         THEN NTAC 3 (POP_ASSUM MP_TAC)
                         THEN Cases_on `WORD_BIT 25 i`  (* IMMEDIATE *)
                         THEN ASM_SIMP_TAC std_ss [iseq_distinct,iclass_distinct,RAA_def,RBA_def,
                                                   LDR_ALU6_T5,LDR_SHIFT_REG_T3,LDR_SHIFT_IMM_T3,LDR_FIELD_T3]
                         THEN Cases_on `WORD_BIT 23 i`  (* UP/DOWN *)
                         THEN Cases_on `WORD_BIT 24 i`  (* PRE/POST *)
                         THEN IMP_RES_TAC MUST_BE_BIT21
                         THEN ASM_SIMP_TAC std_ss [iseq_distinct,iclass_distinct,BIT2_OPC,BIT3_OPC,ALU6_def,
                                                   ALUOUT_ALU_logic,ALUOUT_ADD,ALUOUT_SUB,UP_DOWN_def,
                                                   REG_READ_SUB8_PC,REGISTER_RANGES,
                                                   BIT_W32_NUM,BITS_W32_NUM,LDR_STR_def,SHIFT_IMMEDIATE_THM2,
                                                   SHIFTER_def,ADDR_MODE2_def,DECODE_LDR_STR_def]
                         THEN IMP_RES_TAC (SPECL [`reg`,`DECODE_MODE cpsr`,`DECODE_MODE cpsr`,`DECODE_MODE cpsr`,
                                                  `WORD_BITS 19 16 i`,`WORD_BITS 15 12 i`] OP_INC_REG2)
                         THEN UNABBREV_TAC `pc`
                         THEN POP_ASSUM_LIST (fn thl => ASSUME_TAC (hd thl))
                         THEN REPEAT (STRIP_GOAL_THEN (fn th => REWRITE_TAC [SYM th]))
                         THEN RW_TAC std_ss [SLICE_ROR_THM,FIELD_def,OP_INC_REG2,SWP_SHIFT,REGISTER_RANGES,
                                             MEM_READ_def,MEM_READ_BYTE_def,MEMREAD_def,MEM_READ_WORD_def]
                     ]
                 ],
               PAT_ASSUM `~(~a \/ b)` (fn th => ASSUME_TAC (REWRITE_RULE [NOT_A_OR_B] th) THEN ASSUME_TAC th)
                 THEN Cases_on `WORD_BITS 15 12 i = 15`
                 THEN ASM_SIMP_TAC std_ss []
                 THEN UNFOLD_STATE
                 THEN ALU_LDR3
                 THEN ALU_LDR4
                 THEN ALU_LDR5
                 THEN NTAC 3 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
                 THENL [
                   NTAC 2 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
                     THEN ASM_SIMP_TAC std_ss [ABS_ARM6_def,NEXT_ARM_def,DECODE_PSR_def,REG_WRITE_WRITE_PC,
                                               REG_WRITE_COMMUTES,REGISTER_RANGES,FETCH_SUB8,BITS_W32_NUM,iclass_distinct]
                     THEN ABBREV_TAC `alu3' = ALUOUT alu3`
                     THEN PAT_ASSUM `x = alu3` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM th]))
                     THEN ABBREV_TAC `alu4' = ALUOUT alu4`
                     THEN PAT_ASSUM `x = alu4` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM th]))
                     THEN ABBREV_TAC `alu5' = ALUOUT alu5`
                     THEN PAT_ASSUM `x = alu5` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM th]))
                     THEN NTAC 3 (POP_ASSUM MP_TAC)
                     THEN Cases_on `WORD_BIT 25 i`  (* IMMEDIATE *)
                     THEN ASM_SIMP_TAC std_ss [iseq_distinct,iclass_distinct,RAA_def,RBA_def,
                                               LDR_ALU6_T5,LDR_SHIFT_REG_T3,LDR_SHIFT_IMM_T3,LDR_FIELD_T3]
                     THEN Cases_on `WORD_BIT 23 i`  (* UP/DOWN *)
                     THEN ASM_SIMP_TAC std_ss [iseq_distinct,iclass_distinct,BIT2_OPC,BIT3_OPC,ALU6_def,
                                               ALUOUT_ALU_logic,ALUOUT_ADD,ALUOUT_SUB,UP_DOWN_def,
                                               REG_READ_SUB8_PC,REGISTER_RANGES,
                                               BIT_W32_NUM,BITS_W32_NUM,LDR_STR_def,SHIFT_IMMEDIATE_THM2,
                                               SHIFTER_def,ADDR_MODE2_def,DECODE_LDR_STR_def]
                     THEN POP_ASSUM_LIST (K ALL_TAC)
                     THEN REPEAT (STRIP_GOAL_THEN (fn th => REWRITE_TAC [SYM th]))
                     THEN RW_TAC std_ss [SLICE_ROR_THM,FIELD_def,OP_REG,SWP_SHIFT,
                                         MEM_READ_def,MEM_READ_BYTE_def,MEMREAD_def,MEM_READ_WORD_def],
                   ASM_SIMP_TAC std_ss [ABS_ARM6_def,NEXT_ARM_def,DECODE_PSR_def,REG_WRITE_WRITE_PC,
                                        REG_WRITE_COMMUTES,REGISTER_RANGES,FETCH_SUB8,BITS_W32_NUM,iclass_distinct]
                     THEN ABBREV_TAC `alu3' = ALUOUT alu3`
                     THEN PAT_ASSUM `x = alu3` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM th]))
                     THEN ABBREV_TAC `alu4' = ALUOUT alu4`
                     THEN PAT_ASSUM `x = alu4` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM th]))
                     THEN ABBREV_TAC `alu5' = ALUOUT alu5`
                     THEN PAT_ASSUM `x = alu5` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM th]))
                     THEN NTAC 3 (POP_ASSUM MP_TAC)
                     THEN Cases_on `WORD_BIT 25 i`  (* IMMEDIATE *)
                     THEN ASM_SIMP_TAC std_ss [iseq_distinct,iclass_distinct,RAA_def,RBA_def,
                                               LDR_ALU6_T5,LDR_SHIFT_REG_T3,LDR_SHIFT_IMM_T3,LDR_FIELD_T3]
                     THEN Cases_on `WORD_BIT 23 i`  (* UP/DOWN *)
                     THEN ASM_SIMP_TAC std_ss [iseq_distinct,iclass_distinct,BIT2_OPC,BIT3_OPC,ALU6_def,
                                               ALUOUT_ALU_logic,ALUOUT_ADD,ALUOUT_SUB,UP_DOWN_def,
                                               REG_READ_SUB8_PC,REGISTER_RANGES,
                                               BIT_W32_NUM,BITS_W32_NUM,LDR_STR_def,SHIFT_IMMEDIATE_THM2,
                                               SHIFTER_def,ADDR_MODE2_def,DECODE_LDR_STR_def]
                     THEN IMP_RES_TAC (SPECL [`reg`,`DECODE_MODE cpsr`,`WORD_BITS 15 12 i`] OP_INC_REG)
                     THEN UNABBREV_TAC `pc`
                     THEN POP_ASSUM_LIST (fn thl => ASSUME_TAC (hd thl))
                     THEN REPEAT (STRIP_GOAL_THEN (fn th => REWRITE_TAC [SYM th]))
                     THEN RW_TAC std_ss [SLICE_ROR_THM,FIELD_def,SWP_SHIFT,REGISTER_RANGES,
                                         MEM_READ_def,MEM_READ_BYTE_def,MEMREAD_def,MEM_READ_WORD_def]
                 ]
             ], (* str *)
           IMP_RES_TAC STR_IMP_BITS
             THEN Cases_on `~WORD_BIT 24 i \/ WORD_BIT 21 i`
             THENL [
               PAT_ASSUM `~a \/ b` (fn th => ASSUME_TAC (REWRITE_RULE [NOT_A_OR_B] th) THEN ASSUME_TAC th)
                 THEN Cases_on `WORD_BITS 19 16 i = 15`
                 THEN ASM_SIMP_TAC std_ss []
                 THEN UNFOLD_STATE
                 THEN NTAC 2 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
                 THENL [
                   ALU_STR3
                     THEN ALU_STR4
                     THEN NTAC 2 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
                     THEN ASM_SIMP_TAC std_ss [ABS_ARM6_def,NEXT_ARM_def,DECODE_PSR_def,REG_WRITE_WRITE_PC,
                                               REG_WRITE_COMMUTES,REGISTER_RANGES,FETCH_SUB8,BITS_W32_NUM,iclass_distinct]
                     THEN NTAC 2 (POP_ASSUM (fn th => REWRITE_TAC [SYM th]))
                     THEN Cases_on `WORD_BIT 25 i`  (* IMMEDIATE *)
                     THEN ASM_SIMP_TAC std_ss [iseq_distinct,iclass_distinct,RAA_def,RBA_def,
                                               SHIFTER_def,FIELD_def,LSL_ZERO]
                     THEN Cases_on `WORD_BIT 23 i`  (* UP/DOWN *)
                     THEN Cases_on `WORD_BIT 24 i`  (* PRE/POST *)
                     THEN IMP_RES_TAC MUST_BE_BIT21
                     THEN ASM_SIMP_TAC std_ss [iseq_distinct,iclass_distinct,BIT2_OPC,BIT3_OPC,ALU6_def,
                                               ALUOUT_ALU_logic,ALUOUT_ADD,ALUOUT_SUB,UP_DOWN_def,
                                               REG_READ_SUB8_PC,REGISTER_RANGES,
                                               BIT_W32_NUM,BITS_W32_NUM,LDR_STR_def,SHIFT_IMMEDIATE_THM2,
                                               ADDR_MODE2_def,DECODE_LDR_STR_def]
                     THEN UNABBREV_TAC `pc`
                     THEN POP_ASSUM_LIST (K ALL_TAC)
                     THEN RW_TAC bool_ss [OP_REG,INC_PC_READ,REGISTER_RANGES],
                   ASM_SIMP_TAC std_ss [ABS_ARM6_def,NEXT_ARM_def,DECODE_PSR_def,REG_WRITE_WRITE_PC,
                                        REG_WRITE_COMMUTES,REGISTER_RANGES,FETCH_SUB8,BITS_W32_NUM,iclass_distinct]
                     THEN Cases_on `WORD_BIT 25 i`  (* IMMEDIATE *)
                     THEN ASM_SIMP_TAC std_ss [iseq_distinct,iclass_distinct,RAA_def,RBA_def,
                                               SHIFTER_def,FIELD_def,LSL_ZERO]
                     THEN Cases_on `WORD_BIT 23 i`  (* UP/DOWN *)
                     THEN Cases_on `WORD_BIT 24 i`  (* PRE/POST *)
                     THEN IMP_RES_TAC MUST_BE_BIT21
                     THEN ASM_SIMP_TAC std_ss [iseq_distinct,iclass_distinct,BIT2_OPC,BIT3_OPC,ALU6_def,
                                               ALUOUT_ALU_logic,ALUOUT_ADD,ALUOUT_SUB,UP_DOWN_def,
                                               REG_READ_SUB8_PC,REGISTER_RANGES,
                                               BIT_W32_NUM,BITS_W32_NUM,LDR_STR_def,SHIFT_IMMEDIATE_THM2,
                                               ADDR_MODE2_def,DECODE_LDR_STR_def]
                     THEN PAT_ASSUM `~(a = 15)` (fn th => ASSUME_TAC th
                                                           THEN SIMP_TAC std_ss [PIPE_OKAY_def,PIPECHANGE_def,ALIGN_EQ_def,FETCH_SUB8,
                                                                        th,WORD_ADD_SUB,GSYM WORD_ADD_SUB_SYM,ADD4_SUB8_THM])
                     THEN ONCE_REWRITE_TAC [CONJ_COMM]
                     THEN UNABBREV_TAC `pc`
                     THEN POP_ASSUM_LIST (fn thl => ASSUME_TAC (hd thl))
                     THEN RW_TAC bool_ss [OP_REG,INC_PC_READ,OP_INC_REG,REGISTER_RANGES]
                     THEN FULL_SIMP_TAC bool_ss []
                 ],
               ASM_SIMP_TAC std_ss []
                 THEN PAT_ASSUM `~(~a \/ b)` (fn th => ASSUME_TAC (REWRITE_RULE [NOT_A_OR_B] th) THEN ASSUME_TAC th)
                 THEN UNFOLD_STATE
                 THEN NTAC 2 (UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) [])
                 THEN ASM_SIMP_TAC std_ss [ABS_ARM6_def,NEXT_ARM_def,DECODE_PSR_def,REG_WRITE_WRITE_PC,
                                           REG_WRITE_COMMUTES,REGISTER_RANGES,FETCH_SUB8,BITS_W32_NUM,iclass_distinct]
                 THEN Cases_on `WORD_BIT 25 i`  (* IMMEDIATE *)
                 THEN ASM_SIMP_TAC std_ss [iseq_distinct,iclass_distinct,RAA_def,RBA_def,SHIFTER_def,FIELD_def,LSL_ZERO]
                 THEN Cases_on `WORD_BIT 23 i`  (* UP/DOWN *)
                 THEN ASM_SIMP_TAC std_ss [iseq_distinct,iclass_distinct,BIT2_OPC,BIT3_OPC,ALU6_def,
                                           ALUOUT_ALU_logic,ALUOUT_ADD,ALUOUT_SUB,UP_DOWN_def,
                                           REG_READ_SUB8_PC,REGISTER_RANGES,
                                           BIT_W32_NUM,BITS_W32_NUM,LDR_STR_def,SHIFT_IMMEDIATE_THM2,
                                           ADDR_MODE2_def,DECODE_LDR_STR_def]
                 THEN SIMP_TAC std_ss [PIPE_OKAY_def,PIPECHANGE_def,ALIGN_EQ_def,FETCH_SUB8,
                                       WORD_ADD_SUB,GSYM WORD_ADD_SUB_SYM,ADD4_SUB8_THM]
                 THEN ONCE_REWRITE_TAC [CONJ_COMM]
                 THEN UNABBREV_TAC `pc`
                 THEN POP_ASSUM_LIST (K ALL_TAC)
                 THEN RW_TAC std_ss [OP_REG,INC_PC_READ,NOOP_REG,REGISTER_RANGES]
                 THEN FULL_SIMP_TAC bool_ss []
             ],  (* br *)
           UNFOLD_STATE
             THEN UNFOLD_NEXT THEN ASM_SIMP_TAC (std_ss++CORE3_ss) []
             THEN ALU_BR3
             THEN ALU_BR4
             THEN ALU_BR5
             THEN Cases_on `WORD_BIT 24 i`
             THEN NTAC 2 (UNFOLD_NEXT THEN ASM_SIMP_TAC (arith_ss++CORE3_ss) [])
             THEN ASM_SIMP_TAC arith_ss [ABS_ARM6_def,NEXT_ARM_def,DECODE_PSR_def,REG_WRITE_WRITE_PC,REG_WRITE_WRITE_R14,
                                         REG_WRITE_COMMUTES,REGISTER_RANGES,FETCH_SUB8,BITS_W32_NUM,iclass_distinct]
             THEN ASM_SIMP_TAC arith_ss [BIT_W32_NUM,BITS_W32_NUM,BRANCH_def,DECODE_BRANCH_def,REG_WRITE_COMMUTES]
             THEN POP_ASSUM (K ALL_TAC)
             THEN NTAC 3 (POP_ASSUM (fn th => REWRITE_TAC [SYM th]))
             THEN ASM_SIMP_TAC std_ss [iseq_distinct,iclass_distinct,RAA_def,RBA_def,SHIFTER_def,FIELD_def,LSL_ZERO,LSL_TWO]
             THEN ASM_SIMP_TAC arith_ss [iseq_distinct,iclass_distinct,FETCH_SUB8,REG_READ_SUB8_PC,REGISTER_RANGES,
                                       REG_WRITE_COMMUTES,ALU6_def,ALUOUT_ALU_logic,ALUOUT_ADD,REG_WRITE_READ_R14]
             THEN PAT_ASSUM `x = pc` (fn th => REWRITE_TAC [SYM th,ONE_COMPw_THREE_ADD])
             THEN POP_ASSUM_LIST (K ALL_TAC)
             THEN RW_TAC std_ss [ONE_COMPw_THREE_ADD,GSYM LINK_REG,GSYM BRANCH_REG,PC_READ_MODE_FREE],
             (* swi_ex *)
           UNFOLD_STATE
             THEN ALU_SWI3
             THEN PSR_SWI3
             THEN ALU_SWI4
             THEN PSR_SWI4
             THEN NTAC 3 (UNFOLD_NEXT THEN ASM_SIMP_TAC (arith_ss++CORE3_ss) [])
             THEN ASM_SIMP_TAC arith_ss [ABS_ARM6_def,NEXT_ARM_def,DECODE_PSR_def,REG_WRITE_WRITE_PC,
                                         REG_WRITE_COMMUTES,REGISTER_RANGES,FETCH_SUB8,BITS_W32_NUM,iclass_distinct]
             THEN RULE_ASSUM_TAC (SIMP_RULE arith_ss [iseq_distinct,iclass_distinct,SYM software,
                                                      PSRDAT_def,SHIFTER_def,PSRA_def,AREGN1_def,RAA_def,RBA_def,ALU6_def])
             THEN ASM_SIMP_TAC arith_ss [iseq_distinct,iclass_distinct,exception2num_thm,
                                         BIT_W32_NUM,BITS_W32_NUM,PSRA_def,FETCH_SUB8,
                                         RBA_def,SWI_def,EXCEPTION_def,AREGN1_def,SHIFTER_def,LSL_ZERO,
                                         GSYM ONE_COMPw_THREE_ADD,ALU6_def,ALUOUT_ALU_logic,ALUOUT_ADD]
             THEN NTAC 4 (POP_ASSUM (fn th => SIMP_TAC arith_ss [SYM th,ALUOUT_ALU_logic,REG_WRITE_WRITE_R14,
                                                                 REG_WRITE_READ_R14,DECODE_MODE_THM,CPSR_WRITE_READ]))
             THEN RW_TAC std_ss [PSR_WRITE_COMM,GSYM LINK_REG,PC_READ_MODE_FREE],
             (* undef *)
           UNFOLD_STATE
             THEN ALU_UNDEF3
             THEN PSR_UNDEF3
             THEN ALU_UNDEF4
             THEN PSR_UNDEF4
             THEN NTAC 4 (UNFOLD_NEXT THEN ASM_SIMP_TAC (arith_ss++CORE3_ss) [])
             THEN ASM_SIMP_TAC arith_ss [ABS_ARM6_def,NEXT_ARM_def,DECODE_PSR_def,REG_WRITE_WRITE_PC,
                                         REG_WRITE_COMMUTES,REGISTER_RANGES,FETCH_SUB8,BITS_W32_NUM,iclass_distinct]
             THEN RULE_ASSUM_TAC (SIMP_RULE arith_ss [iseq_distinct,iclass_distinct,SYM undefined,
                                                      PSRDAT_def,SHIFTER_def,PSRA_def,AREGN1_def,RAA_def,RBA_def,ALU6_def])
             THEN ASM_SIMP_TAC arith_ss [iseq_distinct,iclass_distinct,exception2num_thm,
                                         BIT_W32_NUM,BITS_W32_NUM,PSRA_def,FETCH_SUB8,
                                         RBA_def,SWI_def,EXCEPTION_def,AREGN1_def,SHIFTER_def,LSL_ZERO,
                                         GSYM ONE_COMPw_THREE_ADD,ALU6_def,ALUOUT_ALU_logic,ALUOUT_ADD]
             THEN NTAC 4 (POP_ASSUM (fn th => SIMP_TAC arith_ss [SYM th,ALUOUT_ALU_logic,REG_WRITE_WRITE_R14,
                                                                 REG_WRITE_READ_R14,DECODE_MODE_THM,CPSR_WRITE_READ]))
             THEN RW_TAC std_ss [PSR_WRITE_COMM,GSYM LINK_REG,PC_READ_MODE_FREE],
           FULL_SIMP_TAC bool_ss [DECODE_INST_NOT_UNEXEC]
        ]
    ]
);

val ARM6_COR_ONE = GEN_ALL (SIMP_RULE bool_ss [] ARM6_COR_LEM1);

val CORRECT_ARM6 = store_thm("CORRECT_ARM6",
  `CORRECT STATE_ARM STATE_ARM6 IMM_ARM6 ABS_ARM6`,
  SIMP_TAC bool_ss [MATCH_MP TC_I_LEMMA STATE_ARM_THM,ARM6_TIME_CON_IMM,
                    ONE_STEP_THM,IMM_ARM6_UNIFORM,ARM6_DATA_ABSTRACTION]
    THEN REPEAT STRIP_TAC
    THEN MAP_EVERY Cases_on [`a`,`d`,`c`]
    THEN REWRITE_TAC [INIT,ARM6_COR_ZERO,ARM6_COR_ONE]
);

(* -------------------------------------------------------- *)
 
val _ = export_theory();
