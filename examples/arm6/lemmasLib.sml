(* app load ["bossLib","combinTheory","pairTheory","onestepTheory",
             "word32Theory","armTheory","coreTheory","lemmasTheory"]; *)
open HolKernel boolLib Q Parse bossLib simpLib computeLib combinTheory
     arithmeticTheory pairTheory onestepTheory word32Theory
     armTheory coreTheory lemmasTheory;

infix 8 by;
infix THEN THENC THENL ++;
 
(* -------------------------------------------------------- *)

fun core_rws () =
   let val rws = reduceLib.num_compset()
       val _ = add_thms [
                iclass_distinct,iseq_distinct,GSYM iclass_distinct,GSYM iseq_distinct,
                PCCHANGE_def,RWA_def,DECODE_PSR_def,
                IS_def,ABORTINST_def,IC_def,FST,SND,LET_THM,UNCURRY_DEF,PCWA_def,
                INTSEQ_def,PIPEALL_def,PIPEBLL_def,NEWINST_def,NXTIS_def,DIN_def,
                PIPEAWRITE_def,PIPEBWRITE_def,PIPECWRITE_def,AREG_def,
                PIPEAVAL_def,IREGVAL_def,NBW_def,NRW_def,DINWRITE_def,
                PIPESTATIREGWRITE_def,PIPESTATAWRITE_def,PIPESTATBWRITE_def,
                NEXT_ARM6_def] rws
   in
     rws
end;

fun core2_rws () =
   let val rws = core_rws ()
       val _ = add_thms [SCTRLREGWRITE_def,PSRFBWRITE_def,
                         ALUAWRITE_def,ALUBWRITE_def,PSRWA_def] rws
   in
     rws
end;

fun core3_rws () =
   let val rws = core2_rws ()
       val _ = add_thms [NXTIC_def,BUSA_def,BUSB_def] rws
   in
     rws
end;

val thecore_rws = core_rws ();
val thecore2_rws = core2_rws ();
val thecore3_rws = core3_rws ();

val CORE_CONV = CBV_CONV thecore_rws;
val CORE2_CONV = CBV_CONV thecore2_rws;
val CORE3_CONV = CBV_CONV thecore3_rws;

val CORE_ss = simpLib.SIMPSET
  {convs = [{name = "CORE_CONV", trace = 3,
             key = SOME([], ``NEXT_ARM6 a``), conv = K (K CORE_CONV)}],
   rewrs = [iclass_distinct,iseq_distinct,REG_WRITE_WRITE_PC,TEST_OR_COMP_THM2],
   congs = [], filter = NONE, ac = [], dprocs = []};

val CORE2_ss = simpLib.SIMPSET
  {convs = [{name = "CORE2_CONV", trace = 3,
             key = SOME([], ``NEXT_ARM6 a``), conv = K (K CORE2_CONV)}],
   rewrs = [iclass_distinct,iseq_distinct,REG_WRITE_WRITE_PC,TEST_OR_COMP_THM2],
   congs = [], filter = NONE, ac = [], dprocs = []};

val CORE3_ss = simpLib.SIMPSET
  {convs = [{name = "CORE3_CONV", trace = 3,
             key = SOME([], ``NEXT_ARM6 a``), conv = K (K CORE3_CONV)}],
   rewrs = [iclass_distinct,iseq_distinct,REG_WRITE_WRITE_PC,TEST_OR_COMP_THM2],
   congs = [], filter = NONE, ac = [], dprocs = []};

val SWP_ALU3 = ABBREV_TAC `alu3 = ALU6 swp t3 i ARB
                            (SND
                               (SHIFTER swp t3 i oareg sctrl
                                  (REG_READ6 reg (DECODE_MODE cpsr)
                                     (RBA swp t3 i)) (BIT 29 cpsr)))
                            (BIT 29 cpsr)`;

val SWP_ALU4 = ABBREV_TAC `alu4 = ALU6 swp t4 i ARB
                      (SND
                         (SHIFTER swp t3 i oareg sctrl
                            (REG_READ6 reg (DECODE_MODE cpsr) (RBA swp t3 i))
                            (BIT 29 cpsr))) (BIT 29 cpsr)`;

val SWP_ALU5 = ABBREV_TAC `alu5 = ALU6 swp t5 i ARB
                   (SND
                      (SHIFTER swp t5 i (BITSw 1 0 (ALUOUT alu3)) sctrl
                         (REG_READ6
                            (REG_WRITE reg (DECODE_MODE cpsr) 15
                               (pc + w32 4))
                            (DECODE_MODE cpsr) (RBA swp t5 i)) (BIT 29 cpsr)))
                   (BIT 29 cpsr)`;

val SWP_ALU6 = ABBREV_TAC `alu6 = ALU6 swp t6 i ARB
                (SND
                   (SHIFTER swp t6 i (BITSw 1 0 (ALUOUT alu4)) sctrl
                      (FIELD swp t6 i (BITSw 1 0 (ALUOUT alu4))
                         (MEMREAD mem (ALUOUT alu3))) (BIT 29 cpsr)))
                (BIT 29 cpsr)`;

val MSR_ALU3 = ABBREV_TAC `alu3 = ALU6 mrs_msr t3 i
                      (BUSA mrs_msr t3
                         (if PSRA mrs_msr t3 i then
                            CPSR_READ psr
                          else
                            SPSR_READ psr (DECODE_MODE cpsr))
                         (REG_READ6 reg (DECODE_MODE cpsr) (RAA mrs_msr t3 i)))
                      (SND
                         (SHIFTER mrs_msr t3 i oareg sctrl
                            (BUSB mrs_msr t3 i (FIELD mrs_msr t3 i oareg i)
                               (REG_READ6 reg (DECODE_MODE cpsr)
                                  (RBA mrs_msr t3 i))) (BIT 29 cpsr)))
                      (BIT 29 cpsr)`;

val DP_ALU3 = ABBREV_TAC `alu3 = ALU6 data_proc t3 i
                                   (REG_READ6 reg (DECODE_MODE cpsr) (RAA data_proc t3 i))
                                   (SND
                                      (SHIFTER data_proc t3 i oareg sctrl
                                         (BUSB data_proc t3 i (FIELD data_proc t3 i oareg i)
                                            (REG_READ6 reg (DECODE_MODE cpsr)
                                               (RBA data_proc t3 i))) (BIT 29 cpsr)))
                                   (BIT 29 cpsr)`;

val DP_PSR3 = ABBREV_TAC `psr3 = if FST (if BITw 20 i then (T,T) else (F,ARB)) then
                (if SND (if BITw 20 i then (T,T) else (F,ARB)) then
                   CPSR_WRITE psr
                     (PSRDAT data_proc t3 i (DECODE_MODE cpsr) (AREGN1 F)
                        (CPSR_READ psr)
                        (if PSRA data_proc t3 i then
                           CPSR_READ psr
                         else
                           SPSR_READ psr (DECODE_MODE cpsr)) alu3
                        (FST
                           (SHIFTER data_proc t3 i oareg sctrl
                              (BUSB data_proc t3 i
                                 (FIELD data_proc t3 i oareg i)
                                 (REG_READ6 reg (DECODE_MODE cpsr)
                                    (RBA data_proc t3 i))) (BIT 29 cpsr))))
                 else
                   SPSR_WRITE psr (DECODE_MODE cpsr)
                     (PSRDAT data_proc t3 i (DECODE_MODE cpsr) (AREGN1 F)
                        (CPSR_READ psr)
                        (if PSRA data_proc t3 i then
                           CPSR_READ psr
                         else
                           SPSR_READ psr (DECODE_MODE cpsr)) alu3
                        (FST
                           (SHIFTER data_proc t3 i oareg sctrl
                              (BUSB data_proc t3 i
                                 (FIELD data_proc t3 i oareg i)
                                 (REG_READ6 reg (DECODE_MODE cpsr)
                                    (RBA data_proc t3 i))) (BIT 29 cpsr)))))
              else
                psr`;

val RS_ALU4 = ABBREV_TAC `alu4 = ALU6 reg_shift t4 i
                                  (REG_READ6
                                     (REG_WRITE reg (DECODE_MODE cpsr) 15
                                        (pc + w32 4))
                                     (DECODE_MODE cpsr) (RAA reg_shift t4 i))
                                  (SND
                                     (SHIFTER reg_shift t4 i
                                        (BITSw 1 0 pc)
                                        (REG_READ6 reg (DECODE_MODE cpsr)
                                           (RAA reg_shift t3 i))
                                        (REG_READ6
                                           (REG_WRITE reg (DECODE_MODE cpsr) 15
                                              (pc + w32 4))
                                           (DECODE_MODE cpsr) (RBA reg_shift t4 i))
                                        (BIT 29 cpsr))) (BIT 29 cpsr)`;

val RS_PSR4 = ABBREV_TAC `psr4 = if FST (if BITw 20 i then (T,T) else (F,ARB)) then
                (if SND (if BITw 20 i then (T,T) else (F,ARB)) then
                   CPSR_WRITE psr
                     (PSRDAT reg_shift t4 i (DECODE_MODE cpsr) (AREGN1 F)
                        (CPSR_READ psr)
                        (if PSRA reg_shift t4 i then
                           CPSR_READ psr
                         else
                           SPSR_READ psr (DECODE_MODE cpsr)) alu4
                        (FST
                           (SHIFTER reg_shift t4 i
                              (BITSw 1 0 pc)
                              (REG_READ6 reg (DECODE_MODE cpsr)
                                 (RAA reg_shift t3 i))
                              (REG_READ6
                                 (REG_WRITE reg (DECODE_MODE cpsr) 15
                                    (pc + w32 4))
                                 (DECODE_MODE cpsr) (RBA reg_shift t4 i))
                              (BIT 29 cpsr))))
                 else
                   SPSR_WRITE psr (DECODE_MODE cpsr)
                     (PSRDAT reg_shift t4 i (DECODE_MODE cpsr) (AREGN1 F)
                        (CPSR_READ psr)
                        (if PSRA reg_shift t4 i then
                           CPSR_READ psr
                         else
                           SPSR_READ psr (DECODE_MODE cpsr)) alu4
                        (FST
                           (SHIFTER reg_shift t4 i
                              (BITSw 1 0 pc)
                              (REG_READ6 reg (DECODE_MODE cpsr)
                                 (RAA reg_shift t3 i))
                              (REG_READ6
                                 (REG_WRITE reg (DECODE_MODE cpsr) 15
                                    (pc + w32 4))
                                 (DECODE_MODE cpsr) (RBA reg_shift t4 i))
                              (BIT 29 cpsr)))))
              else
                psr`;

val ALU_LDR3 = ABBREV_TAC `alu3 = ALU6 ldr t3 i (REG_READ6 reg (DECODE_MODE cpsr) (RAA ldr t3 i))
                          (SND (SHIFTER ldr t3 i oareg sctrl
                           (if ~BITw 25 i then FIELD ldr t3 i oareg i else REG_READ6 reg (DECODE_MODE cpsr) (RBA ldr t3 i)) (BIT 29 cpsr)))
                               (BIT 29 cpsr)`;

val ALU_LDR4 = ABBREV_TAC `alu4 = ALU6 ldr t4 i (REG_READ6 reg (DECODE_MODE cpsr) (RAA ldr t3 i))
                  (SND (SHIFTER ldr t3 i oareg sctrl
                    (if ~BITw 25 i then FIELD ldr t3 i oareg i else REG_READ6 reg (DECODE_MODE cpsr) (RBA ldr t3 i)) (BIT 29 cpsr)))
                               (BIT 29 cpsr)`;

val ALU_LDR5 = ABBREV_TAC `alu5 = ALU6 ldr t5 i ARB
                         (SND
                            (SHIFTER ldr t5 i (BITSw 1 0 (ALUOUT alu3)) sctrl
                               (FIELD ldr t5 i (BITSw 1 0 (ALUOUT alu3))
                                  (MEMREAD mem (ALUOUT alu3))) (BIT 29 cpsr)))
                         (BIT 29 cpsr)`;

val ALU_STR3 = ABBREV_TAC `alu3 = ALU6 str t3 i (REG_READ6 reg (DECODE_MODE cpsr) (RAA str t3 i))
                (SND (SHIFTER str t3 i oareg sctrl
                      (if ~BITw 25 i then FIELD str t3 i oareg i else REG_READ6 reg (DECODE_MODE cpsr) (RBA str t3 i))
                      (BIT 29 cpsr))) (BIT 29 cpsr)`;

val ALU_STR4 = ABBREV_TAC `alu4 = ALU6 str t4 i
                      (REG_READ6 reg (DECODE_MODE cpsr) (RAA str t3 i))
                      (SND (SHIFTER str t3 i oareg sctrl
                        (if ~BITw 25 i then FIELD str t3 i oareg i else REG_READ6 reg (DECODE_MODE cpsr) (RBA str t3 i))
                            (BIT 29 cpsr))) (BIT 29 cpsr)`;

val ALU_BR3 = ABBREV_TAC `alu3 = ALU6 br t3 i
                      (REG_READ6 reg (DECODE_MODE cpsr) (RAA br t3 i))
                            (SND (SHIFTER br t3 i oareg sctrl (FIELD br t3 i oareg i) (BIT 29 cpsr))) (BIT 29 cpsr)`;

val ALU_BR4 = ABBREV_TAC `alu4 = ALU6 br t4 i
               (REG_READ6 reg (DECODE_MODE cpsr) (RAA br t3 i))
              (SND (SHIFTER br t4 i (BITSw 1 0 pc) sctrl
               (REG_READ6 (REG_WRITE reg (DECODE_MODE cpsr) 15 (pc + w32 4))
                               (DECODE_MODE cpsr) (RBA br t4 i)) (BIT 29 cpsr))) (BIT 29 cpsr)`;

val ALU_BR5 = ABBREV_TAC `alu5 = ALU6 br t5 i (w32 3)
                (SND
                   (SHIFTER br t5 i (BITSw 1 0 (ALUOUT alu3)) sctrl
                      (REG_READ6
                         (REG_WRITE
                            (REG_WRITE reg (DECODE_MODE cpsr) 15
                               (ALUOUT alu3 + w32 4)) (DECODE_MODE cpsr) 14
                            (ALUOUT alu4)) (DECODE_MODE cpsr) (RBA br t5 i))
                      (BIT 29 cpsr))) (BIT 29 cpsr)`;

val ALU_SWI3 = ABBREV_TAC `alu3 = ALU6 swi_ex t3 i
                         (REG_READ6 reg (DECODE_MODE cpsr) (RAA swi_ex t3 i))
                         (SND
                            (SHIFTER swi_ex t3 i oareg sctrl
                               (REG_READ6 reg (DECODE_MODE cpsr)
                                  (RBA swi_ex t3 i)) (BIT 29 cpsr)))
                         (BIT 29 cpsr)`;

val PSR_SWI3 = ABBREV_TAC `psr3 = CPSR_WRITE psr
                (PSRDAT swi_ex t3 i (DECODE_MODE cpsr) (AREGN1 F)
                   (CPSR_READ psr)
                   (if PSRA swi_ex t3 i then
                      CPSR_READ psr
                    else
                      SPSR_READ psr (DECODE_MODE cpsr)) alu3
                   (FST
                      (SHIFTER swi_ex t3 i oareg sctrl
                         (REG_READ6 reg (DECODE_MODE cpsr) (RBA swi_ex t3 i))
                         (BIT 29 cpsr))))`;

val ALU_SWI4 = ABBREV_TAC `alu4 = ALU6 swi_ex t4 i
                        (REG_READ6 reg (DECODE_MODE cpsr) (RAA swi_ex t3 i))
                        (SND
                           (SHIFTER swi_ex t4 i
                              (BITSw 1 0 pc) sctrl
                              (REG_READ6
                                 (REG_WRITE reg (DECODE_MODE cpsr) 15
                                    (pc + w32 4))
                                 (DECODE_MODE (w2n (CPSR_READ psr3)))
                                 (RBA swi_ex t4 i))
                              (BIT 29 (w2n (CPSR_READ psr3)))))
                        (BIT 29 (w2n (CPSR_READ psr3)))`;

val PSR_SWI4 = ABBREV_TAC `psr4 = SPSR_WRITE psr3 (DECODE_MODE (w2n (CPSR_READ psr3)))
         (PSRDAT swi_ex t4 i (DECODE_MODE (w2n (CPSR_READ psr3)))
            (AREGN1 F) (CPSR_READ psr3)
            (if PSRA swi_ex t3 i then
               CPSR_READ psr
             else
               SPSR_READ psr (DECODE_MODE cpsr)) alu4
            (FST
               (SHIFTER swi_ex t4 i (BITSw 1 0 pc) sctrl
                  (REG_READ6
                     (REG_WRITE reg (DECODE_MODE cpsr) 15
                        (pc + w32 4))
                     (DECODE_MODE (w2n (CPSR_READ psr3)))
                     (RBA swi_ex t4 i)) (BIT 29 (w2n (CPSR_READ psr3))))))`;

val ALU_UNDEF3 = ABBREV_TAC `alu3 = ALU6 swi_ex t3
                             (MEMREAD mem (pc - w32 4))
                             (REG_READ6 reg (DECODE_MODE cpsr)
                                (RAA swi_ex t3
                                   (MEMREAD mem
                                      (pc - w32 4))))
                             (SND
                                (SHIFTER swi_ex t3
                                   (MEMREAD mem
                                      (pc - w32 4))
                                   (BITSw 1 0 pc) sctrl
                                   (REG_READ6 reg (DECODE_MODE cpsr)
                                      (RBA swi_ex t3
                                         (MEMREAD mem
                                            (pc -
                                             w32 4)))) (BIT 29 cpsr)))
                             (BIT 29 cpsr)`;

val PSR_UNDEF3 = ABBREV_TAC `psr3 = CPSR_WRITE psr
                (PSRDAT swi_ex t3
                   (MEMREAD mem (pc - w32 4))
                   (DECODE_MODE cpsr) (AREGN1 T) (CPSR_READ psr)
                   (if
                      PSRA swi_ex t3
                        (MEMREAD mem (pc - w32 4))
                    then
                      CPSR_READ psr
                    else
                      SPSR_READ psr (DECODE_MODE cpsr)) alu3
                   (FST
                      (SHIFTER swi_ex t3
                         (MEMREAD mem (pc - w32 4))
                         (BITSw 1 0 pc) sctrl
                         (REG_READ6 reg (DECODE_MODE cpsr)
                            (RBA swi_ex t3
                               (MEMREAD mem (pc - w32 4))))
                         (BIT 29 cpsr))))`;

val ALU_UNDEF4 = ABBREV_TAC `alu4 = ALU6 swi_ex t4
                        (MEMREAD mem (pc - w32 4))
                        (REG_READ6 reg (DECODE_MODE cpsr)
                           (RAA swi_ex t3
                              (MEMREAD mem
                                 (pc - w32 4))))
                        (SND
                           (SHIFTER swi_ex t4
                              (MEMREAD mem (pc - w32 4))
                              (BITSw 1 0 (pc + w32 4))
                              sctrl
                              (REG_READ6
                                 (REG_WRITE reg (DECODE_MODE cpsr) 15
                                    (pc + w32 4 +
                                     w32 4))
                                 (DECODE_MODE (w2n (CPSR_READ psr3)))
                                 (RBA swi_ex t4
                                    (MEMREAD mem
                                       (pc - w32 4))))
                              (BIT 29 (w2n (CPSR_READ psr3)))))
                        (BIT 29 (w2n (CPSR_READ psr3)))`;

val PSR_UNDEF4 = ABBREV_TAC `psr4 = PSRDAT swi_ex t4
                           (MEMREAD mem (pc - w32 4))
                           (DECODE_MODE (w2n (CPSR_READ psr3))) (AREGN1 F)
                           (CPSR_READ psr3)
                           (if
                              PSRA swi_ex t3
                                (MEMREAD mem
                                   (pc - w32 4))
                            then
                              CPSR_READ psr
                            else
                              SPSR_READ psr (DECODE_MODE cpsr)) alu4
                           (FST
                              (SHIFTER swi_ex t4
                                 (MEMREAD mem
                                    (pc - w32 4))
                                 (BITSw 1 0
                                    (pc + w32 4)) sctrl
                                 (REG_READ6
                                    (REG_WRITE reg (DECODE_MODE cpsr) 15
                                       (pc + w32 4 +
                                        w32 4))
                                    (DECODE_MODE (w2n (CPSR_READ psr3)))
                                    (RBA swi_ex t4
                                       (MEMREAD mem
                                          (pc - w32 4))))
                                 (BIT 29 (w2n (CPSR_READ psr3)))))`;

val UNFOLD_STATE = ONCE_REWRITE_TAC [STATE_ARM6_COR]
                       THEN ASM_SIMP_TAC std_ss [INIT_ARM6_def,NXTIC_def,
                                   iclass_distinct,IC_def,ABORTINST_def,DECODE_PSR_def];

val UNFOLD_NEXT = ONCE_REWRITE_TAC [FUNPOW_EVAL] THEN SIMP_TAC arith_ss [FUNPOW];

val finish_rws = [INIT_ARM6_def,DECODE_PSR_def,NXTIC_def,MEM_WRITE_READ,REG_WRITE_READ_PC,
                  REG_WRITE_COMMUTES,ADD_SUBw,ADD4_SUB8_THM];

val FINISH_OFF = STRIP_TAC
        THEN POP_ASSUM (fn th => REWRITE_TAC [SYM th])
        THEN RW_TAC std_ss finish_rws;

val FINISH_OFF2 = POP_ASSUM_LIST (K ALL_TAC)
             THEN STRIP_TAC
             THEN POP_ASSUM (fn th => REWRITE_TAC [SYM th])
             THEN RW_TAC arith_ss finish_rws;

val UNFOLD_SPEC = ONCE_REWRITE_TAC [STATE_ARM_COR] THEN ASM_SIMP_TAC arith_ss [STATE_ARM_def];

(* -------------------------------------------------------- *)
