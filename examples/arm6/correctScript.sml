(* app load ["pred_setSimps","io_onestepTheory","word32Theory","armTheory","word32Lib","memoryTheory",
             "coreTheory","lemmasTheory","lemmasLib","compLib","blockTheory","multTheory","interruptsTheory"]; *)
open HolKernel boolLib bossLib Q compLib lemmasLib arithmeticTheory word32Theory io_onestepTheory 
     armTheory coreTheory lemmasTheory blockTheory multTheory interruptsTheory memoryTheory;

(* -------------------------------------------------------- *)

val _ = new_theory "correct";

val _ = numLib.prefer_num();

val std_ss = std_ss ++ boolSimps.LET_ss;
val arith_ss = arith_ss ++ boolSimps.LET_ss;

val PBETA_TAC = PairRules.PBETA_TAC;
val PBETA_RULE = PairRules.PBETA_RULE;

(* -------------------------------------------------------- *)
(* val _ = Count.counting_thms true; *)
(* -------------------------------------------------------- *)

val DUR_IC_WELL = prove(
  `!ic ireg rs i. 0 < DUR_IC ic ireg rs i`,
  RW_TAC arith_ss [DUR_IC_def]
);

val DUR_ARM6_WELL = store_thm("DUR_ARM6_WELL",
  `!x. 0 < DUR_ARM6 x`,
  Cases THEN Cases_on `a` THEN Cases_on `d` THEN Cases_on `c`
    THEN RW_TAC arith_ss [DECODE_PSR_def,DUR_ARM6_def,DUR_X_def,DUR_IC_WELL]
);

val IMM_ARM6_THM = store_thm("IMM_ARM6_THM",
  `UIMMERSION IMM_ARM6 ARM6_SPEC DUR_ARM6`,
  RW_TAC stdi_ss [UIMMERSION_def,DUR_ARM6_WELL,IMM_ARM6_def,ARM6_SPEC_def]
);

val IMM_ARM6_UNIFORM = store_thm("IMM_ARM6_UNIFORM",
  `UNIFORM IMM_ARM6 ARM6_SPEC`,
  REWRITE_TAC [UNIFORM_def]
    THEN EXISTS_TAC `DUR_ARM6`
    THEN REWRITE_TAC [IMM_ARM6_THM]
);

val IMM_ARM6_ONE = MATCH_MP UIMMERSION_ONE (CONJ STATE_ARM6_IMAP_INIT IMM_ARM6_THM);

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val ARM6_DATA_ABSTRACTION = store_thm("ARM6_DATA_ABSTRACTION",
  `DATA_ABSTRACTION ABS_ARM6 (state_out_state o ARM6_SPEC 0) (state_out_state o ARM_SPEC 0)`,
  RW_TAC bool_ss [MATCH_MP DATA_ABSTRACTION_I (CONJ STATE_ARM_THM3 STATE_ARM6_IMAP_INIT)]
    THEN Cases_on `a` THEN Cases_on `s`
    THEN EXISTS_TAC `ARM6 (DP (ADD8_PC f) f0 areg din alua alub dout)
                      (CTRL pipea pipeaval pipeb pipebval w iregval
                         ointstart onewinst endinst obaselatch opipebll nxtic nxtis
                         nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
                         (exception2num e) mrq2 nbw nrw sctrlreg psrfb oareg mask
                         orp oorp mul mul2 borrow2 mshift)`
    THEN SIMP_TAC std_ss [ABS_ARM6_def,SUB8_INV,INIT_ARM6_def,num2exception_exception2num]
);

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val STRM_ARM6_LEM = prove(
  `!x. (x = <|state := ARM6 (DP reg psr areg din alua alub dout)
              (CTRL pipea pipeaval pipeb pipebval ireg iregval
                ointstart onewinst endinst obaselatch opipebll nxtic nxtis
                nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
                aregn mrq2 nbw nrw sctrlreg psrfb oareg
                mask orp oorp mul mul2 borrow2 mshift); inp :=i|>) ==>
  i IN STRM_ARM6 ==> PROJ_NRESET (i (IMM_ARM6 x 1 - 1))`,
  REPEAT STRIP_TAC
    THEN ASM_SIMP_TAC (std_ss++STATE_INP_ss) [IMM_ARM6_ONE,INIT_ARM6_def,DUR_ARM6_def,DUR_X,DECODE_PSR]
    THEN COND_CASES_TAC
    THENL [
      POP_ASSUM MP_TAC THEN PAT_ABBREV_TAC `d = DUR_IC xic xireg xrs xi`
        THEN STRIP_TAC THEN FULL_SIMP_TAC std_ss []
        THEN POP_ASSUM (SPEC_THEN `d - 1` ASSUME_TAC)
        THEN UNABBREV_TAC `d`
        THEN FULL_SIMP_TAC arith_ss [IS_RESET_def,DUR_IC_WELL],
      FULL_SIMP_TAC std_ss [(REWRITE_RULE [PROVE [] ``(~a = b) = (a = ~b)``] o GSYM) IS_RESET_def]
        THEN IMP_RES_TAC LEAST_NOT_RESET
        THEN ASM_SIMP_TAC arith_ss []
    ]
);

val lem = simpLib.SIMP_PROVE (srw_ss()) [io_onestepTheory.state_inp_component_equality]
            ``state_inp a b = <|state:= a; inp := b|>``;

val STRM_ARM6_LEMb = prove(
  `!x. x.inp IN STRM_ARM6 ==> ~IS_RESET x.inp (IMM_ARM6 x 1 - 1)`,
  Cases THEN Cases_on `a` THEN Cases_on `d` THEN Cases_on `c`
    THEN SIMP_TAC (std_ss++STATE_INP_ss) [lem,IS_RESET_def,GEN_ALL (SIMP_RULE bool_ss [] STRM_ARM6_LEM)]
);

val STRM_ARM6_THM = store_thm("STRM_ARM6_THM",
  `!x t. x.inp IN STRM_ARM6 ==> (ADVANCE (IMM_ARM6 x 1) x.inp) IN STRM_ARM6`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC STRM_ARM6_LEMb
    THEN FULL_SIMP_TAC bool_ss [IN_DEF,STRM_ARM6_def,ADVANCE_def,IS_RESET_def]
    THEN REPEAT STRIP_TAC
    THENL [
      PAT_ASSUM `!t. a ==> b` (SPEC_THEN `IMM_ARM6 x 1 + t` IMP_RES_TAC)
        THEN Cases_on `t`
        THEN FULL_SIMP_TAC arith_ss [ADD1],
      PAT_ASSUM `!t. ?t2. P` (SPEC_THEN `IMM_ARM6 x 1 + t` STRIP_ASSUME_TAC)
        THEN EXISTS_TAC `t2 - IMM_ARM6 x 1`
        THEN ASM_SIMP_TAC arith_ss []
    ]
);

val ARM6_STREAM_ABSTRACTION = store_thm("ARM6_STREAM_ABSTRACTION",
  `STREAM_ABSTRACTION SMPL_ARM6 UNIV STRM_ARM6`,
  RW_TAC std_ss [STREAM_ABSTRACTION_def,pred_setTheory.IN_UNIV]
    THEN EXISTS_TAC `\t. (T,T,F,F,word_0)`
    THEN SIMP_TAC std_ss [IN_DEF,STRM_ARM6_def,IS_RESET_def,PROJ_NRESET_def]
    THEN STRIP_TAC THEN EXISTS_TAC `t + 1`
    THEN DECIDE_TAC
);

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val ARM6_TCON_LEM0 = store_thm("ARM6_TCON_LEM0",
  `!x. (x = <|state := ARM6 (DP reg psr areg din alua alub dout)
              (CTRL pipea pipeaval pipeb pipebval ireg iregval
                ointstart onewinst endinst obaselatch opipebll nxtic nxtis
                nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
                aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
                mask orp oorp mul mul2 borrow2 mshift); inp := i|>) ==>
   (INIT_ARM6 (STATE_ARM6 (IMM_ARM6 x 0) x) = STATE_ARM6 (IMM_ARM6 x 0) x)`,
   RW_TAC bool_ss []
     THEN SIMP_TAC (std_ss++STATE_INP_ss)
            [STATE_ARM6_def,IMM_ARM6_def,INIT_ARM6_def,NXTIC_def,MASK_def,exception_BIJ]
);

val ARM6_TCON_ZERO = GEN_ALL (SIMP_RULE bool_ss [] ARM6_TCON_LEM0);

val INIT = REWRITE_RULE [GSYM FUN_EQ_THM] (CONJUNCT1 STATE_ARM6_def);

val ARM6_TIME_CON_IMM = store_thm("ARM6_TIME_CON_IMM",
  `TCON_IMMERSION ARM6_SPEC IMM_ARM6 STRM_ARM6`,
  SIMP_TAC bool_ss [STRM_ARM6_THM,MATCH_MP TCON_IMMERSION_ONE_STEP_THM (CONJ STATE_ARM6_IMAP_INIT IMM_ARM6_UNIFORM)]
    THEN REPEAT STRIP_TAC
    THEN Cases_on `x` THEN Cases_on `a`
    THEN Cases_on `d` THEN Cases_on `c`
    THEN FULL_SIMP_TAC (std_ss++STATE_INP_ss) [lem,ARM6_SPEC_STATE,INIT,ARM6_TCON_ZERO,ARM6_TCON_ONE]
);

(* -------------------------------------------------------- *)

val lem2 = prove(
  `!t1 t2 i. IS_ABORT (ADVANCE t1 i) t2 = IS_ABORT i (t1 + t2)`,
  REPEAT STRIP_TAC
    THEN REWRITE_TAC [FUN_EQ_THM]
    THEN SIMP_TAC arith_ss [IS_ABORT_def,ADVANCE_def]
);

val TCON_SMPL_ARM6 = prove(
  `TCON_SMPL SMPL_ARM6 IMM_ARM6 ARM6_SPEC STRM_ARM6`,
  RW_TAC std_ss [TCON_SMPL_def]
    THEN REWRITE_TAC [FUN_EQ_THM]
    THEN MAP_EVERY ASSUME_TAC [STATE_ARM6_IMAP,IMM_ARM6_UNIFORM,ARM6_TIME_CON_IMM]
    THEN IMP_RES_TAC (GSYM TCON_IMMERSION_COR)
    THEN Cases_on `x`
    THEN FULL_SIMP_TAC (arith_ss++STATE_INP_ss) [GSYM ARM6_SPEC_STATE,COMBINE_def,SMPL_ARM6_def,ADVANCE_def,
           lem2,SMPL_EXC_ARM6_def,SMPL_DATA_ARM6_def,MAP_STRM_def,PACK_def,IMM_LEN_def,ADVANCE_def,
           (GSYM o SIMP_RULE (srw_ss()) [] o GEN_ALL o INST [`x` |-> `state_inp a f`] o SPEC_ALL o
            SIMP_RULE std_ss [TCON_IMMERSION_def]) ARM6_TIME_CON_IMM]
    THEN REPEAT STRIP_TAC
    THEN1 (ASM_REWRITE_TAC [DECIDE ``a + (b + (c + d)) = a + (b + c) +d``] THEN SIMP_TAC arith_ss [])
    THEN POP_ASSUM (fn th => REWRITE_TAC [(GSYM o SPECL [`x + 1`,`t`]) th,(GSYM o SPECL [`x`,`t`]) th]
                     THEN ASSUME_TAC th)
    THEN SIMP_TAC arith_ss []
);

(* -------------------------------------------------------- *)

val SPEC_COND_RATOR = prove(
  `!n b. (if b then n + 2 else n) = (if b then 2 else 0) + n`,
  RW_TAC arith_ss []
);

val [SPEC_COND_RATOR1,SPEC_COND_RATOR2,SPEC_COND_RATOR3,SPEC_COND_RATOR4] =
   map (fn x => (SIMP_RULE arith_ss [] o SPEC x) SPEC_COND_RATOR) [`1`,`2`,`3`,`4`];

val REV_ADD4 = DECIDE ``a + b + c + d = d + c + b + a``;

val COMP_VAL_BIT = prove(
  `!a b c x. (~(\(w,a). w /\ (a = 15)) if c /\ ~(a = 15) then (T,a) else (F,x))`,
  RW_TAC std_ss []
);

val COMP_VAL_BIT2 = prove(
  `!a b c d. (~(\(w,a). w /\ (a = 15)) if (c = 15) \/ (c = d) then (F,b) else (T,c))`,
  RW_TAC std_ss [] THEN FULL_SIMP_TAC bool_ss []
);

val COMP_VAL_BIT3 = prove(
  `!abort rp Rn.
   ((\(rw,a). rw /\ (a = 15))
     (if abort /\ ~(Rn = 15) then
        (T,Rn)
      else
        (if ~abort then (T,rp) else (F,ARB)))) = ~abort /\ (rp = 15)`,
  RW_TAC std_ss [] THEN FULL_SIMP_TAC bool_ss []
);

val COMP_VAL_BIT4 = prove(
  `~(a = 15) ==> (~(\(w,a). w /\ (a = 15)) if b then (T,a) else (F,c))`,
  RW_TAC std_ss [] THEN FULL_SIMP_TAC bool_ss []
);

val COMP_VAL_BIT5 = prove(
  `!abort rp Rn.
    ~(\(rw,a). rw /\ (a = 15))
            (if abort then
               (F,ARB)
             else
               (if ~(WORD_BITS 19 16 ireg = 15) then
                  (T,WORD_BITS 19 16 ireg)
                else
                  (F,ARB)))`,
  RW_TAC std_ss [] THEN FULL_SIMP_TAC bool_ss []
);

val SPEC_PENCZ_THM = (GEN_ALL o REWRITE_RULE [MASKN_ZERO] o SPECL [`n`,`0`] o
                      CONJUNCT1 o SIMP_RULE stdi_ss [] o SPEC `stm`) PENCZ_THM;

val ALU_ABBREV_TAC = with_flag (priming,SOME "")
  (PAT_ABBREV_TAC `alu = ALU6 ic is xireg xborrow2 xmul xdataabt xalua xalub xc`);
val PSR_ABBREV_TAC = with_flag (priming,SOME "") (PAT_ABBREV_TAC `psr = xpsr:psr`);

val FST_COND_RAND = ISPEC `FST` COND_RAND;
val SND_COND_RAND = ISPEC `SND` COND_RAND;
val SUB_SUC1 = DECIDE ``!x. 1 < x ==> (SUC (x - 1) = x)``;

val COND_RAND_RATOR = PROVE [] ``!f b z x y. (if b then f x z else f y z) = f (if b then x else y) z``;
val COND_RATOR_TWO = PROVE [] ``!f g b x y. (if b then f x y else g x y) = (if b then f else g) x y``;
val COND_RAND_RATOR_ROR = (GSYM o ISPEC `$#>>`) COND_RAND_RATOR;

val REG_WRITE_READ_NEQ_15 =
   (SIMP_RULE arith_ss [TO_WRITE_READ6] o INST [`n1` |-> `15`] o SPEC_ALL) REG_WRITE_READ_NEQ;

val PROJ_DATA_EL0 =
  (GSYM o SIMP_RULE std_ss [rich_listTheory.EL,ADVANCE_def] o SPEC `0`) PROJ_DATA_EL;

val REG_WRITEN_WRITE_PC3 =
  (GEN_ALL o SIMP_RULE arith_ss [ADVANCE_def,PROJ_DATA] o DISCH `0 < LENGTH (REGISTER_LIST (w2n ireg))` o
   INST [`i` |-> `ADVANCE 1 i`] o SPEC_ALL) REG_WRITEN_WRITE_PC;

val REG_WRITEN_WRITE_PC4 =
  (GEN_ALL o SIMP_RULE arith_ss [ADVANCE_def,PROJ_DATA] o DISCH `0 < LENGTH (REGISTER_LIST (w2n ireg))` o
   INST [`i` |-> `ADVANCE 1 i`] o SPEC_ALL) REG_WRITEN_WRITE_PC2;

(* -------------------------------------------------------- *)

val PC_CHANGE_RWA = prove(
  `(!ireg list oorp dataabt.
     PCCHANGE (RWA swp t6 ireg list oorp dataabt) =
       (WORD_BITS 15 12 ireg = 15) /\ ~dataabt) /\
   !ireg list oorp dataabt.
     PCCHANGE (RWA ldr t5 ireg list oorp dataabt) =
       (WORD_BITS 15 12 ireg = 15) /\ ~dataabt`,
  RW_TAC stdi_ss [RWA_def,PCCHANGE_def]
);

(* -------------------------------------------------------- *)

val LDM_PENCZ_ZERO =
  (GEN_ALL o REWRITE_RULE [MASKN_ZERO] o INST [`x` |-> `0`] o SPEC_ALL o
   CONJUNCT1 o SIMP_RULE std_ss [] o SPEC `ldm`) PENCZ_THM;

val PENCZ_ONE = prove(
  `!n. 0 < LENGTH (REGISTER_LIST n) ==>
       (PENCZ ldm n (MASKN 16 1 n) = (LENGTH (REGISTER_LIST n) = 1))`,
  REPEAT STRIP_TAC THEN Cases_on `LENGTH (REGISTER_LIST n) = 1`
    THEN ASM_SIMP_TAC arith_ss [PENCZ_THM]
    THEN PROVE_TAC [PENCZ_THM]
);

val NOT_T3 = prove(
  `!b. ~((if b then tm else tn) = t3)`,
  RW_TAC stdi_ss []
);

(* -------------------------------------------------------- *)

val ARM6_COR_LEM0 = store_thm("ARM6_COR_LEM0",
  `!x. (x = <|state := ARM6 (DP reg psr areg din alua alub dout)
               (CTRL pipea pipeaval pipeb pipebval ireg iregval
                ointstart onewinst endinst obaselatch opipebll nxtic nxtis
                nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
                aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
                mask orp oorp mul mul2 borrow2 mshift); inp := i|>) ==>
   (STATE_ARM 0 <|state := ABS_ARM6 x.state; inp := SMPL_ARM6 x|> = ABS_ARM6 (STATE_ARM6 (IMM_ARM6 x 0) x))`,
  RW_TAC bool_ss []
    THEN SIMP_TAC (std_ss++STATE_INP_ss)
           [STATE_ARM_def,STATE_ARM6_def,IMM_ARM6_def,INIT_ARM6_def,ABS_ARM6_def,exception_BIJ]
);

val ARM6_COR_ZERO = GEN_ALL (SIMP_RULE (srw_ss()) [] ARM6_COR_LEM0);

(* -------------------------------------------------------- *)

val (BIT7,BIT6) =
   let val x = CONJUNCTS DECODE_IFMODE_SET_NZCV
       val y = List.nth(x,1)
       val z = List.nth(x,2)
       val f = (GEN_ALL o SIMP_RULE std_ss [BIT_W32_NUM] o
                  SPECL [`FST (a : bool # bool # bool # bool)`,
                         `FST (SND (a : bool # bool # bool # bool))`,
                         `FST (SND (SND (a : bool # bool # bool # bool)))`,
                         `SND (SND (SND (a : bool # bool # bool # bool)))`])
   in
     (f y,f z)
   end;

val ARM6_COR_LEM1 = Count.apply store_thm("ARM6_COR_LEM1",
  `!x. (x = <|state := ARM6 (DP reg psr areg din alua alub dout)
               (CTRL pipea pipeaval pipeb pipebval ireg iregval
                ointstart onewinst endinst obaselatch opipebll nxtic nxtis
                nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
                aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
                mask orp oorp mul mul2 borrow2 mshift); inp := i|>) ==>
    i IN STRM_ARM6 ==>
   (STATE_ARM 1 <|state := ABS_ARM6 x.state; inp := SMPL_ARM6 x|> = ABS_ARM6 (STATE_ARM6 (IMM_ARM6 x 1) x))`,
  RW_TAC bool_ss []
    THEN SIMP_TAC (arith_ss++STATE_INP_ss) [ADD,SMPL_ARM6_def,COMBINE_def,SMPL_EXC_ARM6_def,STATE_ARM_def,
           IMM_LEN_def,UNFOLD_SPEC,IMM_ARM6_def,ABS_ARM6_def,SMPL_DATA_ARM6_def,MAP_STRM_def,PACK_def]
    THEN PAT_ABBREV_TAC `a = ABS_ARM6 (STATE_ARM6 t b)`
    THEN POP_ASSUM (MP_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def])
    THEN ABBREV_TAC `pc = REG_READ6 reg usr 15`
    THEN ABBREV_TAC `cpsr = CPSR_READ psr`
    THEN ABBREV_TAC `nbs = DECODE_MODE (WORD_BITS 4 0 cpsr)`
    THEN SIMP_TAC (srw_ss()++boolSimps.LET_ss) [IMM_ARM6_ONE,INIT_ARM6_def,NXTIC_def,SINIT_def,
           num2exception_exception2num,STATE_ARM6_def,STATE_ARM6_COR,DUR_ARM6_def,DUR_X_def,DECODE_PSR]
    THEN COND_CASES_TAC THEN FULL_SIMP_TAC std_ss []
    THENL [ (* reset *)
      IMP_RES_TAC LEAST_NOT_RESET
        THEN PAT_ASSUM `IS_RESET i t` (K ALL_TAC)
        THEN IMP_RES_TAC LEAST_RESET_GT_TWO
        THEN IMP_RES_TAC PREVIOUS_THREE_RESET
        THEN REPEAT (PAT_ASSUM `~a ==> b` (K ALL_TAC))
        THEN IMP_RES_TAC (DECIDE ``!n. (2 < n) ==> (n = n - 3 + 3)``)
        THEN POP_ASSUM (fn th => ONCE_REWRITE_TAC [th] THEN RULE_ASSUM_TAC (ONCE_REWRITE_RULE [th]))
        THEN REWRITE_TAC [DECIDE ``!a. a + 3 + 3 = 6 + a``]
        THEN REWRITE_TAC [onestepTheory.FUNPOW_COMP]
        THEN PAT_ABBREV_TAC `x = FUNPOW (SNEXT NEXT_ARM6) xt <|state := xa; inp := i|>`
        THEN RULE_ASSUM_TAC (ONCE_REWRITE_RULE [GSYM STATE_FUNPOW_INIT2]) THEN UNABBREV_TAC `x`
        THEN PAT_ABBREV_TAC `x = (FUNPOW (SNEXT NEXT_ARM6) xt <|state := ARM6 xd dc; inp := i|>).state`
        THEN IMP_RES_TAC SPEC_AFTER_NRESET2
        THEN POP_ASSUM (SPEC_THEN `x` ASSUME_TAC)
        THEN POP_ASSUM_LIST (fn thl => ASSUME_TAC (hd thl))
        THEN RW_TAC std_ss [] THEN IMP_RES_TAC AFTER_NRESET2_THM4
        THEN FULL_SIMP_TAC arith_ss [] THEN POP_ASSUM SUBST1_TAC
        THEN SIMP_TAC (srw_ss()) [NEXT_ARM_def,IS_Reset_def,PROJ_Reset_def]
        THEN metisLib.METIS_TAC [TRIPLE_ARM_EX_THM],
      POP_ASSUM (fn th => ASSUME_TAC (MATCH_MP IS_RESET_THM th))
        THEN REVERSE (Cases_on `num2exception aregn2 = software`)
        THEN FULL_SIMP_TAC std_ss [iclass_distinct,IC_def,ABORTINST_def,exception_BIJ]
        THENL [ (* take interrupt *)
          FULL_SIMP_TAC stdi_ss [DUR_IC_def]
            THEN NTAC 3 (UNFOLD_NEXT THEN SWI_EX_TAC THEN ALU_ABBREV_TAC THEN TRY PSR_ABBREV_TAC)
	    THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss) [ABS_ARM6_def,exception2num_thm]
            THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
	    THEN ASM_SIMP_TAC (stdi_ss++BARM_ss) []
	    THEN ABBREV_TAC `alu1' = SND alu1` THEN UNABBREV_TAC `alu1`
	    THEN ABBREV_TAC `alu2' = SND alu2` THEN UNABBREV_TAC `alu2`
	    THEN RULE_ASSUM_TAC (SIMP_RULE (stdi_ss++ALU_ss) [])
	    THEN MAP_EVERY UNABBREV_TAC [`alu2'`,`alu1'`,`psr2`,`psr1`]
	    THEN ASM_SIMP_TAC (std_ss++BARM_ss) [CPSR_WRITE_READ]
	    THEN RW_TAC std_ss ([AC MULT_ASSOC MULT_COMM,PSR_WRITE_COMM,exception_EQ_exception,
                   num2exception_thm,exception2num_thm] @ finish_rws2),
          PAT_ASSUM `Abbrev (cpsr = CPSR_READ psr)` (fn th => FULL_SIMP_TAC bool_ss [th] THEN ASSUME_TAC th)
            THEN REVERSE (Cases_on `CONDITION_PASSED (NZCV (w2n cpsr)) (w2n ireg)`)
            THENL [ (* unexecuted *)
              FULL_SIMP_TAC stdi_ss [DUR_IC_def]
                THEN UNFOLD_NEXT THEN UNEXEC_TAC
        	THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss) [ABS_ARM6_def,exception2num_thm]
                THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
	        THEN ASM_SIMP_TAC (stdi_ss++BARM_ss) []
                THEN ASM_SIMP_TAC std_ss finish_rws2,
              Cases_on `DECODE_INST (w2n ireg)`
                THEN FULL_SIMP_TAC stdi_ss [DUR_IC_def,IS_ABORT_LEM,PC_CHANGE_RWA]
                THENL [ (* swp *)
                  REWRITE_TAC [onestepTheory.FUNPOW_COMP,SPEC_COND_RATOR4]
                    THEN `!t. t < 4 ==> FST (i t)` by PROVE_TAC [DECIDE ``!t. t < 4 ==> t < 6``]
                    THEN NTAC 4 (UNFOLD_NEXT THEN SWP_TAC THEN ALU_ABBREV_TAC)
                    THEN ABBREV_TAC `alu' = SND alu` THEN UNABBREV_TAC `alu`
                    THEN ABBREV_TAC `alu1' = SND alu1` THEN UNABBREV_TAC `alu1`
                    THEN UNABBREV_TAC `alu2`
                    THEN ABBREV_TAC `alu3' = SND alu3` THEN UNABBREV_TAC `alu3`
                    THEN RULE_ASSUM_TAC (SIMP_RULE (stdi_ss++ALU_ss) [])
                    THEN `alu' = alu1'` by FULL_SIMP_TAC bool_ss [] THEN POP_ASSUM SUBST_ALL_TAC
                    THEN Cases_on `(WORD_BITS 15 12 ireg = 15) /\ ~FST (SND (i 1)) /\ ~FST (SND (i 2))`
                    THEN ASM_SIMP_TAC stdi_ss [FUNPOW]
                    THENL [
                      NTAC 2 (UNFOLD_NEXT THEN UNEXEC_TAC)
                        THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss) [ABS_ARM6_def,exception2num_thm],
                      FULL_SIMP_TAC stdi_ss [ABS_ARM6_def,COMP_VAL_BIT4,COND_PAIR,exception2num_thm]]
                    THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
                    THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss++BARM_ss) [COMP_VAL_BIT4,BW_READ_def,
                            (numLib.REDUCE_RULE o SPEC `3`) PROJ_DATA_EL0,
                            (numLib.REDUCE_RULE o SPEC `5`) PROJ_DATA_EL0]
                    THEN FULL_SIMP_TAC (stdi_ss++ALU_ss) [PROJ_DATA,COND_RAND_RATOR_ROR,SLICE_ROR_THM,IF_NEG]
                    THEN MAP_EVERY UNABBREV_TAC [`alu3'`,`alu1'`,`pc`]
                    THEN RW_TAC stdi_ss (RBA_def :: finish_rws2)
                    THEN FULL_SIMP_TAC std_ss [],
                    (* mrs_msr *)
                  Cases_on `WORD_BIT 21 ireg`
                    THEN FULL_SIMP_TAC stdi_ss [RWA_def,PCCHANGE_def]
                    THENL [ (* msr *)
                      UNFOLD_NEXT THEN MRS_MSR_TAC
                        THEN ASM_SIMP_TAC stdi_ss [ABS_ARM6_def,exception2num_thm]
                        THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
                        THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss++BARM_ss) []
                        THEN ASM_SIMP_TAC (stdi_ss++ALU_ss) [SPLIT_WORD_def,BIT_OPC,WORD_BITS118_LEM,
                               FST_COND_RAND,SND_COND_RAND,GSYM IMMEDIATE_THM,IMMEDIATE_THM2]
                        THEN UNABBREV_TAC `pc`
                        THEN ASM_SIMP_TAC stdi_ss finish_rws2
                        THEN Cases_on `USER nbs`
                        THEN Cases_on `WORD_BIT 22 ireg`
                        THEN Cases_on `WORD_BIT 19 ireg`
                        THEN Cases_on `WORD_BIT 16 ireg`
                        THEN ASM_SIMP_TAC stdi_ss ([PROJ_IF_FLAGS_def,DECODE_PSR,BIT_W32_NUM] @ finish_rws2),
                            (* mrs *)
                      Cases_on `WORD_BITS 15 12 ireg = 15`
                        THEN ASM_SIMP_TAC std_ss []
                        THEN UNFOLD_NEXT THEN MRS_MSR_TAC
                        THENL [
                          ALU_ABBREV_TAC THEN NTAC 2 (UNFOLD_NEXT THEN UNEXEC_TAC)
                            THEN ASM_SIMP_TAC stdi_ss [ABS_ARM6_def,exception2num_thm]
                            THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
                            THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss++BARM_ss) []
                            THEN ABBREV_TAC `alu' = SND alu` THEN UNABBREV_TAC `alu`
                            THEN FULL_SIMP_TAC (stdi_ss++ALU_ss) [BIT_OPC,WORD_BITS118_LEM,SND_COND_RAND]
                            THEN UNABBREV_TAC `alu'`
                            THEN RW_TAC std_ss finish_rws2,
                          ASM_SIMP_TAC stdi_ss [ABS_ARM6_def,exception2num_thm]
                            THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
                            THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss++BARM_ss) []
                            THEN ASM_SIMP_TAC (stdi_ss++ALU_ss) (finish_rws2 @ [BIT_OPC,WORD_BITS118_LEM,IF_NEG])
                        ]
                    ],  (* data_proc *)
                  Cases_on `WORD_BIT 24 ireg /\ ~WORD_BIT 23 ireg`
                    THEN POP_ASSUM (fn th => let val th2 = SIMP_RULE stdi_ss [] th in
                                              RULE_ASSUM_TAC (SIMP_RULE stdi_ss [RWA_def,PCCHANGE_def,th2])
                                                THEN ASSUME_TAC th2 THEN ASSUME_TAC th end)
                    THEN ASM_SIMP_TAC stdi_ss [RWA_def,PCCHANGE_def]
                    THENL [ (* Test or Compare *)
                      UNFOLD_NEXT THEN DATA_PROC_TAC
                        THEN ASM_SIMP_TAC stdi_ss [ABS_ARM6_def,exception2num_thm]
                        THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
                        THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss++BARM_ss) []
                        THEN ASM_SIMP_TAC (stdi_ss++ALU_ss) [WORD_BITS118_LEM,GSYM IMMEDIATE_THM,
                               ARITHMETIC_THM,SHIFT_IMMEDIATE_THM2,TEST_OR_COMP_THM,
                               ADDR_MODE1_def,SPSR_READ_THM]
                        THEN PBETA_TAC
                        THEN UNABBREV_TAC `pc`
                        THEN REVERSE (Cases_on `WORD_BIT 20 ireg`)
                        THEN ASM_REWRITE_TAC []
                        THEN1 ASM_SIMP_TAC stdi_ss ([PROJ_IF_FLAGS_def,DECODE_PSR,BIT_W32_NUM] @ finish_rws2)
                        THEN Cases_on `WORD_BIT 25 ireg`
                        THEN ASM_SIMP_TAC (stdi_ss++BARM_ss) [SET_NZC_def,DATA_PROC_IMP_NOT_BIT4]
                        THEN RW_TAC stdi_ss ([SET_NZC_def,BIT7,BIT6] @ finish_rws2),
                      Cases_on `WORD_BITS 15 12 ireg = 15`
                        THEN ASM_REWRITE_TAC []
                        THEN POP_ASSUM (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) THEN ASSUME_TAC th)
                        THEN ASM_SIMP_TAC bool_ss [FUNPOW]
                        THENL [ (* PCCHANGE *)
                          UNFOLD_NEXT THEN DATA_PROC_TAC THEN ALU_ABBREV_TAC THEN PSR_ABBREV_TAC
                            THEN NTAC 2 (UNFOLD_NEXT THEN UNEXEC_TAC)
                            THEN ASM_SIMP_TAC stdi_ss [ABS_ARM6_def,exception2num_thm]
                            THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
                            THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss++BARM_ss)
                                   [TEST_OR_COMP_THM,ADDR_MODE1_def,SHIFT_IMMEDIATE_THM2]
                            THEN PBETA_TAC
                            THEN ASM_SIMP_TAC std_ss [SPSR_READ_THM,PROJ_IF_FLAGS_def,DECODE_PSR,BIT_W32_NUM]
                            THEN RULE_ASSUM_TAC (SIMP_RULE (stdi_ss++ALU_ss) [GSYM IMMEDIATE_THM,WORD_BITS118_LEM])
                            THEN MAP_EVERY UNABBREV_TAC [`psr1`,`alu`]
                            THEN PAT_ASSUM `~a \/ b` (fn th => ASSUME_TAC (REWRITE_RULE [NOT_A_OR_B] th))
                            THEN ASM_SIMP_TAC std_ss [SPSR_READ_THM]
                            THEN Cases_on `WORD_BIT 25 ireg`
                            THEN ASM_SIMP_TAC std_ss [DATA_PROC_IMP_NOT_BIT4]
                            THEN Cases_on `WORD_BIT 20 ireg`
                            THEN ASM_SIMP_TAC (std_ss++BARM_ss) [CPSR_WRITE_READ,SIMP_interrupt2exception2]
                            THEN POP_ASSUM_LIST (K ALL_TAC)
                            THEN RW_TAC std_ss finish_rws2,
                                (* NOT PCCHANGE *)
                          UNFOLD_NEXT THEN DATA_PROC_TAC
                            THEN ASM_SIMP_TAC stdi_ss [ABS_ARM6_def,exception2num_thm]
                            THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
                            THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss++BARM_ss) []
                            THEN ASM_SIMP_TAC (stdi_ss++ALU_ss) [TEST_OR_COMP_THM,ADDR_MODE1_def,SPSR_READ_THM,
                                          SHIFT_IMMEDIATE_THM2,GSYM IMMEDIATE_THM,WORD_BITS118_LEM,ARITHMETIC_THM2]
                            THEN PBETA_TAC
                            THEN UNABBREV_TAC `pc`
                            THEN Cases_on `WORD_BIT 25 ireg`
                            THEN ASM_SIMP_TAC std_ss [DATA_PROC_IMP_NOT_BIT4]
                            THEN Cases_on `WORD_BIT 20 ireg`
                            THEN ASM_SIMP_TAC std_ss [IF_NEG]
                            THEN RW_TAC std_ss ([PROJ_IF_FLAGS_def,DECODE_PSR,BIT_W32_NUM,
                                   BIT7,BIT6,SET_NZC_def] @ finish_rws2)
                        ]
                    ], (* reg_shift *)
                  IMP_RES_TAC REG_SHIFT_IMP_BITS
                    THEN Cases_on `WORD_BIT 24 ireg /\ ~WORD_BIT 23 ireg`
                    THEN POP_ASSUM (fn th => let val th2 = SIMP_RULE stdi_ss [] th in
                           RULE_ASSUM_TAC (SIMP_RULE stdi_ss [RWA_def,PCCHANGE_def,th2])
                             THEN ASSUME_TAC th2 THEN ASSUME_TAC th end)
                    THEN ASM_SIMP_TAC stdi_ss [RWA_def,PCCHANGE_def]
                    THENL [ (* Test or Compare *)
                      NTAC 2 (UNFOLD_NEXT THEN REG_SHIFT_TAC)
                        THEN ASM_SIMP_TAC stdi_ss [ABS_ARM6_def,exception2num_thm]
                        THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
                        THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss++BARM_ss) []
                        THEN ASM_SIMP_TAC (stdi_ss++ALU_ss) [WORD_BITS118_LEM,ARITHMETIC_THM,SHIFT_REGISTER_THM2,
                                                             TEST_OR_COMP_THM,ADDR_MODE1_def,SPSR_READ_THM]
                        THEN PBETA_TAC
                        THEN UNABBREV_TAC `pc`
                        THEN REVERSE (Cases_on `WORD_BIT 20 ireg`)
                        THEN ASM_REWRITE_TAC []
                        THEN1 ASM_SIMP_TAC stdi_ss ([PROJ_IF_FLAGS_def,DECODE_PSR,BIT_W32_NUM] @ finish_rws2)
                        THEN ASM_SIMP_TAC (stdi_ss++BARM_ss) [SET_NZC_def,DATA_PROC_IMP_NOT_BIT4]
                        THEN RW_TAC stdi_ss ([SET_NZC_def,BIT7,BIT6] @ finish_rws2),
                      Cases_on `WORD_BITS 15 12 ireg = 15`
                        THEN ASM_REWRITE_TAC []
                        THEN POP_ASSUM (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) THEN ASSUME_TAC th)
                        THEN NTAC 2 (UNFOLD_NEXT THEN REG_SHIFT_TAC)
                        THENL [ (* PCCHANGE *)
                          ALU_ABBREV_TAC THEN PSR_ABBREV_TAC THEN NTAC 2 (UNFOLD_NEXT THEN UNEXEC_TAC)
                            THEN ASM_SIMP_TAC stdi_ss [ABS_ARM6_def,exception2num_thm]
                            THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
                            THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss++BARM_ss) []
                            THEN ASM_SIMP_TAC std_ss [TEST_OR_COMP_THM,ADDR_MODE1_def,SHIFT_REGISTER_THM2]
                            THEN RULE_ASSUM_TAC (SIMP_RULE (stdi_ss++ALU_ss) [WORD_BITS118_LEM])
                            THEN MAP_EVERY UNABBREV_TAC [`psr1`,`alu`,`pc`]
                            THEN ASM_SIMP_TAC std_ss [SPSR_READ_THM]
                            THEN PBETA_TAC
                            THEN Cases_on `WORD_BIT 20 ireg`
                            THEN RW_TAC std_ss ([PROJ_IF_FLAGS_def,DECODE_PSR,BIT_W32_NUM] @ finish_rws2),
                          ASM_SIMP_TAC stdi_ss [ABS_ARM6_def,exception2num_thm]
                            THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
                            THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss++BARM_ss) []
                            THEN ASM_SIMP_TAC (stdi_ss++ALU_ss) [TEST_OR_COMP_THM,ADDR_MODE1_def,SPSR_READ_THM,
                                                               SHIFT_REGISTER_THM2,WORD_BITS118_LEM,ARITHMETIC_THM2]
                            THEN PBETA_TAC
                            THEN UNABBREV_TAC `pc`
                            THEN Cases_on `WORD_BIT 20 ireg`
                            THEN RW_TAC std_ss ([PROJ_IF_FLAGS_def,DECODE_PSR,BIT_W32_NUM,
                                   SET_NZC_def,BIT7,BIT6] @ finish_rws2)
                        ]
                    ], (* mla_mul *)
                  REWRITE_TAC [GSYM SUC_ONE_ADD,FUNPOW]
                    THEN UNFOLD_NEXT THEN MLA_MUL_TAC
                    THEN ASM_SIMP_TAC arith_ss [iclass_distinct,ISPEC `FST` COND_RAND,ISPEC `SND` COND_RAND,
                           IF_NEG,GSYM WORD_BITS_def,LSL_ZERO,bitsTheory.BITS_ZERO2,COMP_VAL_BIT2,
                           MULT_ALU6_ZERO,TO_WRITE_READ6]
                    THEN REWRITE_TAC [GSYM DE_MORGAN_THM,IF_NEG]
                    THEN PAT_ASSUM `Abbrev (nbs = DECODE_MODE (WORD_BITS 4 0 cpsr))`
                            (fn th => FULL_SIMP_TAC bool_ss [th,DECIDE ``1 + n = n + 1``] THEN ASSUME_TAC th)
                    THEN IMP_RES_TAC MLA_MUL_TN
                     THEN POP_ASSUM (SPECL_THEN 
                            [`sctrlreg`,`psrfb`,`pipebabt`,`pipeb`,`FST (SND (i 0))`,
                             `SND (SND (SND (SND (i 0))))`,`orp`,`oniq`,`onfq`,`FST (SND (SND (SND (i 0))))`,
                             `FST (SND (SND (i 0)))`,
                             `~BIT 6 (w2n cpsr) /\ ~ooonfq \/ pipebabt \/ ~BIT 7 (w2n cpsr) /\ ~oooniq`,
                             `BASELATCH mla_mul t3`,`REG_READ6 reg nbs (WORD_BITS 15 12 ireg)`,`F`,
                             `AREGN1 F F (~BIT 6 (w2n cpsr) /\ ~ooonfq) (~BIT 7 (w2n cpsr) /\ ~oooniq) F pipebabt`,`alua`]
                            STRIP_ASSUME_TAC)
                    THEN POP_ASSUM SUBST1_TAC
                    THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss) [ABS_ARM6_def,exception2num_thm]
                    THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
                    THEN ASM_SIMP_TAC (stdi_ss++BARM_ss) [ALU_multiply_def,MLA_MUL_CARRY_def,MSHIFT_def,SET_NZC_def]
                    THEN UNABBREV_TAC `pc`
                    THEN RW_TAC std_ss ([WORD_ADD_0,CARRY_LEM] @ finish_rws2)
                    THEN FULL_SIMP_TAC stdi_ss ([BIT7,BIT6,
                            PROJ_IF_FLAGS_def,DECODE_PSR,BIT_W32_NUM,SIMP_interrupt2exception4,
                            SIMP_interrupt2exception5] @ finish_rws2),
                    (* ldr *)
                  IMP_RES_TAC LDR_IMP_BITS
                    THEN REWRITE_TAC [onestepTheory.FUNPOW_COMP,SPEC_COND_RATOR3]
                    THEN `!t. t < 3 ==> FST (i t)` by PROVE_TAC [DECIDE ``!t. t < 3 ==> t < 5``]
                    THEN NTAC 2 (UNFOLD_NEXT THEN LDR_TAC THEN ALU_ABBREV_TAC)
                    THEN PBETA_TAC THEN UNFOLD_NEXT THEN LDR_TAC THEN ALU_ABBREV_TAC
                    THEN ABBREV_TAC `alu' = SND alu` THEN UNABBREV_TAC `alu`
                    THEN ABBREV_TAC `alu1' = SND alu1` THEN UNABBREV_TAC `alu1`
                    THEN ABBREV_TAC `alu2' = SND alu2` THEN UNABBREV_TAC `alu2`
                    THEN FULL_SIMP_TAC (stdi_ss++ALU_ss) [SND_COND_RAND,BIT_OPC,
                           UP_DOWN_THM,SND_ROR,IF_NEG,COND_RAND_RATOR_ROR,SLICE_ROR_THM]
                    THEN Cases_on `~WORD_BIT 24 ireg \/ WORD_BIT 21 ireg`
                    THEN POP_ASSUM (fn th => ASSUME_TAC (REWRITE_RULE [NOT_A_OR_B] th) THEN ASSUME_TAC th
                                               THEN ASSUME_TAC (ONCE_REWRITE_RULE [DISJ_SYM] th))
                    THEN Cases_on `(WORD_BITS 15 12 ireg = 15) /\ ~FST (SND (i 1))`
                    THEN ASM_SIMP_TAC stdi_ss [RWA_def,PCCHANGE_def,FUNPOW,COND_PAIR,IS_ABORT_LEM]
                    THENL [
                      NTAC 2 (UNFOLD_NEXT THEN UNEXEC_TAC)
                        THEN Cases_on `WORD_BITS 19 16 ireg = 15`,
                      Cases_on `WORD_BITS 19 16 ireg = 15`
                        THEN POP_ASSUM (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) THEN ASSUME_TAC th)
                        THEN ASM_SIMP_TAC bool_ss [FUNPOW]
                        THENL [NTAC 2 (UNFOLD_NEXT THEN UNEXEC_TAC),ALL_TAC],
                      NTAC 2 (UNFOLD_NEXT THEN UNEXEC_TAC),
                      ALL_TAC
                    ]
                    THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss) [ABS_ARM6_def,exception2num_thm]
                    THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
                    THEN ASM_SIMP_TAC (stdi_ss++BARM_ss) [DECIDE ``!a. ~(~a /\ a)``,COMP_VAL_BIT4,
                                                          BW_READ_def,SHIFT_IMMEDIATE_THM2,ADDR_MODE2_def,
                                                          (numLib.REDUCE_RULE o SPEC `4`) PROJ_DATA_EL0,
                                                          (numLib.REDUCE_RULE o SPEC `2`) PROJ_DATA_EL0]
                    THEN MAP_EVERY UNABBREV_TAC [`alu2'`,`alu1'`,`alu'`,`pc`]
                    THEN RW_TAC std_ss (PROJ_DATA :: finish_rws2)
                    THEN FULL_SIMP_TAC std_ss finish_rws2,
                    (* str *)
                  IMP_RES_TAC STR_IMP_BITS
                    THEN `!t. t < 2 ==> FST (i t)` by PROVE_TAC [DECIDE ``!t. t < 2 ==> t < 4``]
                    THEN Cases_on `~WORD_BIT 24 ireg \/ WORD_BIT 21 ireg`
                    THEN POP_ASSUM (fn th => ASSUME_TAC (REWRITE_RULE [NOT_A_OR_B] th) THEN ASSUME_TAC th
                                               THEN ASSUME_TAC (ONCE_REWRITE_RULE [DISJ_SYM] th))
                    THENL [
                      REWRITE_TAC [onestepTheory.FUNPOW_COMP,SPEC_COND_RATOR2]
                        THEN NTAC 2 (UNFOLD_NEXT THEN STR_TAC THEN ALU_ABBREV_TAC)
                        THEN ABBREV_TAC `alu' = SND alu` THEN UNABBREV_TAC `alu`
                        THEN ABBREV_TAC `alu1' = SND alu1` THEN UNABBREV_TAC `alu1`
                        THEN RULE_ASSUM_TAC (SIMP_RULE (stdi_ss++ALU_ss) [IF_NEG,SND_COND_RAND,BIT_OPC,UP_DOWN_THM])
                        THEN PAT_ASSUM `!t. t < (if b then x else y) ==> z` MP_TAC
                        THEN Cases_on `WORD_BITS 19 16 ireg = 15`
                        THEN ASM_SIMP_TAC stdi_ss [RWA_def,PCCHANGE_def,FUNPOW]
                        THENL [STRIP_TAC THEN NTAC 2 (UNFOLD_NEXT THEN UNEXEC_TAC),ALL_TAC]
                        THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss) [ABS_ARM6_def,exception2num_thm]
                        THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
                        THEN ASM_SIMP_TAC (stdi_ss++BARM_ss) [SHIFT_IMMEDIATE_THM2,ADDR_MODE2_def,RBA_def]
                        THEN MAP_EVERY UNABBREV_TAC [`alu1'`,`alu'`,`pc`]
                        THEN RW_TAC std_ss finish_rws2
                        THEN FULL_SIMP_TAC std_ss [],
                      ASM_SIMP_TAC stdi_ss [RWA_def,PCCHANGE_def]
                        THEN NTAC 2 (UNFOLD_NEXT THEN STR_TAC)
                        THEN ASM_SIMP_TAC stdi_ss [ABS_ARM6_def,exception2num_thm]
                        THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
                        THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss++BARM_ss) []
                        THEN ASM_SIMP_TAC (stdi_ss++ALU_ss) [SND_COND_RAND,BIT_OPC,UP_DOWN_THM,SHIFT_IMMEDIATE_THM2,ADDR_MODE2_def]
                        THEN UNABBREV_TAC `pc`
                        THEN RW_TAC std_ss ([PROJ_IF_FLAGS_def,DECODE_PSR,BIT_W32_NUM] @ finish_rws2)
                    ],  (* ldm *)
                  ONCE_REWRITE_TAC [REV_ADD4] THEN ONCE_REWRITE_TAC [onestepTheory.FUNPOW_COMP]
                    THEN IMP_RES_TAC (simpLib.SIMP_PROVE arith_ss [] ``(!t. t < (2 + x) + y + z ==>
                                                                       FST (i t)) ==> (!t. t < 2 ==> FST (i t))``)
                    THEN NTAC 2 (UNFOLD_NEXT THEN LDM_TAC)
                    THEN IMP_RES_TAC DECODE_INST_LDM
                    THEN Cases_on `WORD_BITS 15 0 ireg = 0`
                    THEN ASM_SIMP_TAC stdi_ss [MASKN_150,PENCZ_RP_150,MASKN16_2,MASKN16_1,PENCZ_THM3,COMP_VAL_BIT]
                    THENL [
                      IMP_RES_TAC PENCZ_THM2
                        THEN IMP_RES_TAC WORD_BITS_150_ZERO
                        THEN ASM_REWRITE_TAC [ADD_CLAUSES,SUB_0,FUNPOW]
                        THEN UNFOLD_NEXT THEN LDM_TAC
                        THEN ASM_SIMP_TAC stdi_ss [COMP_VAL_BIT5]
                        THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss) [ABS_ARM6_def,exception2num_thm]
                        THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
                        THEN ASM_SIMP_TAC (stdi_ss++BARM_ss) [FST_COND_RAND,LSL_ZERO,ALUOUT_ALU_logic]
                        THEN PBETA_TAC
                        THEN Cases_on `WORD_BIT 22 ireg`
                        THEN Cases_on `FST (SND (i 1))`
                        THEN Cases_on `WORD_BITS 19 16 ireg = 15`
                        THEN ASM_SIMP_TAC stdi_ss [USER_usr]
                        THEN RW_TAC std_ss ([SND_ADDR_MODE4,LEAST_ABORT_ZERO_ISA,WB_ADDRESS_ZERO,
                                             rich_listTheory.FIRSTN,CONJUNCT1 REG_WRITEN_def,
                                             LDM_LIST_EMPTY,REG_WRITE_WRITE,LENGTH_ADDR_MODE4,
                                             REG_WRITE_READ_NEQ,REG_WRITE_READ_NEQ_15,
                                             PROJ_IF_FLAGS_def,DECODE_PSR,BIT_W32_NUM] @ finish_rws2)
                        THEN FULL_SIMP_TAC std_ss [],
                      `0 < LENGTH (REGISTER_LIST (w2n ireg))` by FULL_SIMP_TAC arith_ss [PENCZ_THM2]
                        THEN IMP_RES_TAC (simpLib.SIMP_PROVE arith_ss []
                                                    ``0 < x /\ (!t. t < (2 + (x - 1)) + y + z ==>
                                                       FST (i t)) ==> (!t. t < SUC x ==> FST (i t))``)
                        THEN NTAC 2 ALU_ABBREV_TAC
                        THEN ASM_SIMP_TAC arith_ss [FST_COND_RAND,onestepTheory.FUNPOW_COMP,LSL_ZERO,PENCZ_ONE,
                                                    GSYM ADVANCE_COMP,LDM_PENCZ_ZERO,NOT_T3]
                        THEN IMP_RES_TAC NEXT_CORE_LDM_TN_W1
                        THEN POP_ASSUM (SPECL_THEN [`sctrlreg`,
                               `if WORD_BIT 21 ireg /\ ~(WORD_BITS 19 16 ireg = 15) then
                                  REG_WRITE (REG_WRITE reg nbs 15 (pc + w32 4)) nbs (WORD_BITS 19 16 ireg) (SND alu)
                                else
                                  REG_WRITE reg nbs 15 (pc + w32 4)`,`SPSR_READ psr nbs`,`psr`,`pipebabt`,`pipeb`,
                               `FST (SND (i 0))`,`SND (SND (SND (SND (i 0))))`,`FST (SND (SND (SND (i 0))))`,
                               `FST (SND (SND (i 0)))`,`FST (SND (SND (SND (i 1))))`,`FST (SND (SND (i 1)))`,
                               `FST (SND (i 1)) \/ ~BIT 6 (w2n cpsr) /\ ~onfq \/ pipebabt \/ ~BIT 7 (w2n cpsr) /\ ~oniq`,
                               `WORD_BITS 1 0 (SND alu1)`,`BITS HB 2 ARB`,`BITS 1 0 ARB`,`ARB`,
                               `REG_READ6 (REG_WRITE reg nbs 15 (pc + w32 4)) nbs ARB`,
                               `REG_READ6 (REG_WRITE reg nbs 15 (pc + w32 4)) usr 15`,`ARB`,`SND alu1`,
                               `AREGN1 F (FST (SND (i 1))) (~BIT 6 (w2n cpsr) /\ ~onfq)
                                       (~BIT 7 (w2n cpsr) /\ ~oniq) F pipebabt`,
                               `REG_READ6 reg nbs (WORD_BITS 19 16 ireg)`,`OFFSET ldm t4 ireg (WORD_BITS 15 0 ireg)`]
                              STRIP_ASSUME_TAC)
                        THEN ASM_SIMP_TAC stdi_ss []
                        THEN POP_ASSUM (K ALL_TAC)
                        THEN `FST (i (LENGTH (REGISTER_LIST (w2n ireg)) + 1))`
                          by metisLib.METIS_TAC [DECIDE ``!w. 0 < w ==> w + 1 < 2 + (w - 1) + 1 + x``]
                        THEN UNFOLD_NEXT THEN LDM_TAC
                        THEN ASM_SIMP_TAC arith_ss [(SIMP_RULE std_ss [] o
                               SPEC `?s. s < LENGTH (REGISTER_LIST (w2n ireg)) /\ FST (SND (i (s + 1)))`) COMP_VAL_BIT3,
                               COND_PAIR,SND_COND_RAND,ALUOUT_ALU_logic,LSL_ZERO,RP_LAST_15]
                        THEN Cases_on `WORD_BIT 15 ireg /\
                                         ~(?s. s < LENGTH (REGISTER_LIST (w2n ireg)) /\ FST (SND (i (s + 1))))`
                        THEN ASM_SIMP_TAC std_ss [FUNPOW]
                        THENL [
                          FULL_SIMP_TAC stdi_ss []
                            THEN IMP_RES_TAC RP_LAST_15
                            THEN `FST (i (LENGTH (REGISTER_LIST (w2n ireg)) + 1 + 1))`
                              by metisLib.METIS_TAC [DECIDE ``!w. 0 < w ==> w + 1 + 1 < 2 + (w - 1) + 1 + 2``]
                            THEN `FST (i (LENGTH (REGISTER_LIST (w2n ireg)) + 1 + 2))`
                              by metisLib.METIS_TAC [DECIDE ``!w. 0 < w ==> w + 1 + 2 < 2 + (w - 1) + 1 + 2``]
                            THEN NTAC 2 (UNFOLD_NEXT THEN UNEXEC_TAC)
                            THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss) [ABS_ARM6_def,exception2num_thm]
                            THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
                            THEN ASM_SIMP_TAC (stdi_ss++BARM_ss) []
                            THEN PBETA_TAC
                            THEN MAP_EVERY UNABBREV_TAC [`alu1`,`alu`,`pc`]
                            THEN Cases_on `WORD_BIT 22 ireg`
                            THEN Cases_on `USER nbs`
                            THEN Cases_on `WORD_BITS 19 16 ireg = 15`
                            THEN ASM_SIMP_TAC stdi_ss [USER_usr]
                            THEN UNABBREV_TAC `cpsr`
                            THEN RW_TAC arith_ss ([(SIMP_RULE arith_ss [] o
                                   INST [`n` |-> `LENGTH (REGISTER_LIST ireg) + 3`] o
                                   SPEC_ALL) REGISTER_LIST_LDM_THM,
                                   (GEN_ALL o SIMP_RULE arith_ss [ADD1] o DISCH `0 < n` o
                                   INST [`n` |-> `n - 1`] o SPEC_ALL) REG_WRITEN_SUC,
                                   SUB_SUC1,SND_ADDR_MODE4,REG_WRITEN_WRITE_PC4,GSYM FIRST_ADDRESS,
                                   ALUOUT_ALU_logic,LENGTH_ADDR_MODE4,GSYM WB_ADDRESS,REG_READ_WRITEN_PC,
                                   ADVANCE_def,LSL_ZERO,REG_WRITE_WRITEN_PC,REG_WRITEN_WRITE_PC3,
                                   PROJ_IF_FLAGS_def,DECODE_PSR,BIT_W32_NUM] @ finish_rws2)
                            THEN FULL_SIMP_TAC stdi_ss ([SPSR_READ_THM2,CPSR_READ_WRITE,PROJ_DATA] @ finish_rws2),
                          RULE_ASSUM_TAC (PURE_REWRITE_RULE [
                                     metisLib.METIS_PROVE [] ``~(?s. s < l /\ FST (SND (i (s + 1)))) =
                                                            (!s. ~(s < l) \/ ~FST (SND (i (s + 1))))``])
                            THEN ABBREV_TAC `abort = ?s. s < LENGTH (REGISTER_LIST (w2n ireg)) /\ FST (SND (i (s + 1)))`
                            THEN ISPECL_THEN [`ireg`,`i`] SUBST1_TAC ((GEN_ALL o REWRITE_RULE [IS_ABORT_LEM] o
                                    CONV_RULE (REDEPTH_CONV FORALL_NOT_CONV) o
                                    ONCE_REWRITE_CONV [GSYM DE_MORGAN_THM])
                                    ``!s.  ~(s < LENGTH (REGISTER_LIST (w2n ireg))) \/ ~FST (SND (i (s + 1)))``)
                            THEN ASM_SIMP_TAC pureSimps.pure_ss []
                            THEN FULL_SIMP_TAC stdi_ss [FUNPOW]
                            THENL [
                              `~(RP ldm (w2n ireg) (MASKN 16 (LENGTH (REGISTER_LIST (w2n ireg)) - 1) (w2n ireg)) = 15)`
                                 by ASM_SIMP_TAC arith_ss [RP_LAST_15]
                                THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss) [ABS_ARM6_def,exception2num_thm]
                                THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
                                THEN ASM_SIMP_TAC (stdi_ss++BARM_ss) [LSL_ZERO,ALUOUT_ALU_logic,LEAST_ABORT_ISA]
                                THEN `abort ==> (LEAST s. FST (SND (i (s + 1)))) < LENGTH (REGISTER_LIST (w2n ireg))`
                                  by metisLib.METIS_TAC [LEAST_ABORT_LT2]
                                THEN MAP_EVERY UNABBREV_TAC [`alu1`,`alu`,`pc`]
                                THEN PBETA_TAC
                                THEN ASM_SIMP_TAC arith_ss [LSL_ZERO,ALUOUT_ALU_logic,GSYM WB_ADDRESS,
                                                            GSYM FIRST_ADDRESS,state_arm_ex_11,state_arm_11]
                                THEN Cases_on `abort`
                                THEN FULL_SIMP_TAC stdi_ss []
                                THEN Cases_on `WORD_BIT 21 ireg`
                                THEN Cases_on `WORD_BITS 19 16 ireg = 15`
                                THEN ASM_SIMP_TAC stdi_ss [USER_usr]
                                THEN RW_TAC arith_ss ([(SIMP_RULE arith_ss [] o
                                       INST [`n` |-> `LENGTH (REGISTER_LIST ireg) + 1`] o
                                       SPEC_ALL) REGISTER_LIST_LDM_THM,
                                       (GEN_ALL o SIMP_RULE arith_ss [ADD1] o DISCH `0 < n` o
                                       INST [`n` |-> `n - 1`] o SPEC_ALL) REG_WRITEN_SUC,
                                       SUB_SUC1,REG_WRITEN_COMMUTE_PC,LENGTH_ADDR_MODE4,
                                       REG_WRITEN_COMMUTES,REG_READ_WRITEN_PC2,ADVANCE_def,
                                       REG_READ_WRITEN_PC,REG_WRITE_WRITEN_PC,REG_WRITEN_WRITE_PC4,
                                       REG_WRITEN_WRITE_PC3,SND_ADDR_MODE4] @ finish_rws2)
                                THEN FULL_SIMP_TAC stdi_ss ([PROJ_DATA,USER_usr,CPSR_READ_WRITE,
                                       PROJ_IF_FLAGS_def,DECODE_PSR,BIT_W32_NUM] @ finish_rws2)
                                THEN IMP_RES_TAC (DECIDE ``!x. x < 1 ==> (x = 0)``)
                                THEN PAT_ASSUM `Abbrev q` (fn th =>
                                       ASSUME_TAC (MATCH_MP (SPEC `1` LEAST_ABORT_ISA)
                                                            (REWRITE_RULE [markerTheory.Abbrev_def] th)))
                                THEN ASM_SIMP_TAC std_ss [CONJUNCT1 REG_WRITEN_def],
                              ASM_SIMP_TAC (stdi_ss++STATE_INP_ss) [ABS_ARM6_def,exception2num_thm]
                                THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
                                THEN ASM_SIMP_TAC (stdi_ss++BARM_ss) [LSL_ZERO,ALUOUT_ALU_logic,LEAST_ABORT_ISA]
                                THEN `(LEAST s. FST (SND (i (s + 1)))) < LENGTH (REGISTER_LIST (w2n ireg))`
                                  by metisLib.METIS_TAC [LEAST_ABORT_LT2]
                                THEN MAP_EVERY UNABBREV_TAC [`alu1`,`alu`,`pc`]
                                THEN PBETA_TAC
                                THEN ASM_SIMP_TAC arith_ss [LSL_ZERO,ALUOUT_ALU_logic,GSYM WB_ADDRESS,
                                                            GSYM FIRST_ADDRESS,state_arm_ex_11,state_arm_11]
                                THEN Cases_on `WORD_BIT 21 ireg`
                                THEN Cases_on `WORD_BITS 19 16 ireg = 15`
                                THEN ASM_SIMP_TAC stdi_ss [USER_usr]
                                THEN RW_TAC (stdi_ss++numSimps.ARITH_ss) ([(SIMP_RULE arith_ss [] o
                                       INST [`n` |-> `LENGTH (REGISTER_LIST ireg) + 1`] o
                                       SPEC_ALL) REGISTER_LIST_LDM_THM,
                                       (GEN_ALL o SIMP_RULE arith_ss [ADD1] o DISCH `1 < n` o
                                       INST [`n` |-> `n - 1`] o SPEC_ALL) REG_WRITEN_SUC,
                                       SUB_SUC1,REG_WRITEN_COMMUTE_PC,REG_WRITEN_COMMUTES,
                                       REG_READ_WRITEN_PC2,REG_READ_WRITEN_PC,REG_WRITE_WRITEN_PC,
                                       REG_WRITEN_WRITE_PC3,SND_ADDR_MODE4,ADVANCE_def,
                                       LENGTH_ADDR_MODE4,REG_WRITEN_WRITE_PC4] @ finish_rws2)
                                THEN UNABBREV_TAC `cpsr`
                                THEN FULL_SIMP_TAC stdi_ss ([LSL_ZERO,PROJ_DATA,USER_usr,CPSR_READ_WRITE,
                                       PROJ_IF_FLAGS_def,DECODE_PSR,BIT_W32_NUM] @ finish_rws2)
                                THEN IMP_RES_TAC (DECIDE ``!x. x < 1 ==> (x = 0)``)
                                THEN PAT_ASSUM `Abbrev q` (fn th =>
                                       ASSUME_TAC (MATCH_MP (SPEC `1` LEAST_ABORT_ISA)
                                                            (REWRITE_RULE [markerTheory.Abbrev_def] th)))
                                THEN ASM_SIMP_TAC std_ss [CONJUNCT1 REG_WRITEN_def]
                            ]
                        ]
                    ], (* stm *)
                  ONCE_REWRITE_TAC [ADD_COMM] THEN REWRITE_TAC [onestepTheory.FUNPOW_COMP]
                    THEN IMP_RES_TAC (simpLib.SIMP_PROVE arith_ss [] ``(!t. t < (2 + x) ==> FST (i t)) ==>
                                                                       (!t. t < 2 ==> FST (i t))``)
                    THEN NTAC 2 (UNFOLD_NEXT THEN STM_TAC THEN ALU_ABBREV_TAC)
                    THEN IMP_RES_TAC DECODE_INST_STM
                    THEN Cases_on `WORD_BITS 15 0 ireg = 0`
                    THEN ASM_SIMP_TAC stdi_ss [LSL_ZERO,MASKN_150,PENCZ_RP_150,MASKN16_1,PENCZ_THM3,
                           FST_COND_RAND,COMP_VAL_BIT]
                    THENL [
                      IMP_RES_TAC PENCZ_THM2
                        THEN ASM_REWRITE_TAC [SUB_0,FUNPOW]
                        THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss) [ABS_ARM6_def,exception2num_thm]
                        THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
                        THEN ASM_SIMP_TAC (stdi_ss++BARM_ss) [LSL_ZERO,ALUOUT_ALU_logic]
                        THEN PBETA_TAC
                        THEN MAP_EVERY UNABBREV_TAC [`alu1`,`pc`]
                        THEN Cases_on `WORD_BITS 19 16 ireg = 15`
                        THEN RW_TAC std_ss ([LSL_ZERO,ALUOUT_ALU_logic,SND_ADDR_MODE4,GSYM WB_ADDRESS,
                               WB_ADDRESS_ZERO,PROJ_IF_FLAGS_def,DECODE_PSR,BIT_W32_NUM] @ finish_rws2),
                      `~PENCZ stm (w2n ireg) (ONECOMP 16 0)` by FULL_SIMP_TAC arith_ss [SPEC_PENCZ_THM,PENCZ_THM2]
                        THEN Cases_on `LENGTH (REGISTER_LIST (w2n ireg)) = 1`
                        THENL [
                          `PENCZ stm (w2n ireg) (MASKN 16 1 (w2n ireg))` by PROVE_TAC [PENCZ_THM]
                            THEN ASM_REWRITE_TAC [SUB_EQUAL_0,FUNPOW]
                            THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss) [ABS_ARM6_def,exception2num_thm]
                            THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
                            THEN ASM_SIMP_TAC (stdi_ss++BARM_ss) []
                            THEN PBETA_TAC
                            THEN MAP_EVERY UNABBREV_TAC [`alu1`,`alu`,`pc`]
                            THEN ASM_SIMP_TAC arith_ss [FST_HD_FST_ADDR_MODE4]
                            THEN Cases_on `WORD_BITS 19 16 ireg = 15`
                            THEN RW_TAC arith_ss ([SND_ADDR_MODE4,MASKN_ZERO,GSYM WB_ADDRESS,GSYM FIRST_ADDRESS,
                                   RP_LT_16_0,LSL_ZERO,ALUOUT_ALU_logic,
                                   REWRITE_RULE [word_0,word_1] WORD_MULT_CLAUSES,
                                   PROJ_IF_FLAGS_def,DECODE_PSR,BIT_W32_NUM] @ finish_rws2),
                          `1 < LENGTH (REGISTER_LIST (w2n ireg))` by FULL_SIMP_TAC arith_ss [PENCZ_THM2]
                            THEN `~(PENCZ stm (w2n ireg) (MASKN 16 1 (w2n ireg)))` by PROVE_TAC [PENCZ_THM]
                            THEN ASM_SIMP_TAC stdi_ss [LSL_ZERO,MASK_def,MASKN16_2b,GSYM ADVANCE_COMP]
                            THEN IMP_RES_TAC (simpLib.SIMP_PROVE arith_ss [] ``!w. 1 < w ==> (!t. t < 2 + (w - 1) ==>
                                                                              FST (i t)) ==> (!t. t < SUC w ==> FST (i t))``)
                            THEN IMP_RES_TAC NEXT_CORE_STM_TN_W1
                            THEN POP_ASSUM (SPECL_THEN [`sctrlreg`,
                                   `if WORD_BIT 21 ireg /\ ~(WORD_BITS 19 16 ireg = 15) then
                                      REG_WRITE (REG_WRITE reg nbs 15 (pc + w32 4))
                                        (if WORD_BIT 22 ireg then usr else nbs)
                                        (WORD_BITS 19 16 ireg) (SND alu1)
                                    else
                                      REG_WRITE reg nbs 15 (pc + w32 4)`,
                                   `SPSR_READ psr (if WORD_BIT 22 ireg then usr else nbs)`,`pipebabt`,`pipeb`,
                                   `FST (SND (i 0))`,`SND (SND (SND (SND (i 0))))`,`FST (SND (SND (SND (i 0))))`,
                                   `FST (SND (SND (i 0)))`,`FST (SND (SND (SND (i 1))))`,`FST (SND (SND (i 1)))`,
                                   `FST (SND (i 1)) \/ ~BIT 6 (w2n cpsr) /\ ~onfq \/ pipebabt \/
                                    ~BIT 7 (w2n cpsr) /\ ~oniq`,`BASELATCH stm t4`,`WORD_BITS 1 0 (SND alu)`,
                                   `BITS HB 2 ARB`,`BITS 1 0 ARB`,`ARB`,
                                   `REG_READ6 (REG_WRITE reg nbs 15 (pc + w32 4))
                                       (if WORD_BIT 22 ireg then usr else nbs)
                                       (RP stm (w2n ireg) (ONECOMP 16 0))`,
                                   `ireg`,`FST (SND (i 1))`,`ARB`,`SND alu`,
                                   `AREGN1 F (FST (SND (i 1))) (~BIT 6 (w2n cpsr) /\ ~onfq)
                                          (~BIT 7 (w2n cpsr) /\ ~oniq) F pipebabt`,
                                   `REG_READ6 reg nbs (WORD_BITS 19 16 ireg)`,`OFFSET stm t4 ireg (WORD_BITS 15 0 ireg)`]
                                 STRIP_ASSUME_TAC)
                            THEN POP_ASSUM SUBST1_TAC
                            THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss) [ABS_ARM6_def,exception2num_thm]
                            THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
                            THEN ASM_SIMP_TAC (stdi_ss++BARM_ss) []
                            THEN PBETA_TAC
                            THEN MAP_EVERY UNABBREV_TAC [`alu1`,`alu`,`pc`]
                            THEN RW_TAC arith_ss ([LSL_ZERO,ALUOUT_ALU_logic,SND_ADDR_MODE4,FST_HD_FST_ADDR_MODE4,
                                   GSYM WB_ADDRESS,GSYM FIRST_ADDRESS,SIMP_interrupt2exception4,
                                   SIMP_interrupt2exception5,PROJ_IF_FLAGS_def,DECODE_PSR,
                                   BIT_W32_NUM] @ finish_rws2)
                        ]
                    ], (* br *)
                  UNFOLD_NEXT THEN BR_TAC THEN ALU_ABBREV_TAC
                    THEN Cases_on `WORD_BIT 24 ireg`
                    THEN NTAC 2 (UNFOLD_NEXT THEN BR_TAC THEN TRY ALU_ABBREV_TAC)
                    THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss) [ABS_ARM6_def,exception2num_thm]
                    THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
                    THEN ASM_SIMP_TAC (stdi_ss++BARM_ss) []
                    THEN ABBREV_TAC `alu' = SND alu` THEN UNABBREV_TAC `alu`
                    THEN ABBREV_TAC `alu1' = SND alu1` THEN TRY (UNABBREV_TAC `alu1`)
                    THEN ABBREV_TAC `alu2' = SND alu2` THEN TRY (UNABBREV_TAC `alu2`)
                    THEN RULE_ASSUM_TAC (SIMP_RULE (stdi_ss++ALU_ss) [GSYM ONE_COMP_THREE_ADD,OFFSET_def])
                    THEN MAP_EVERY UNABBREV_TAC [`alu2'`,`alu1'`,`alu'`]
                    THEN RW_TAC std_ss finish_rws2,
                    (* swi_ex *)
                  NTAC 3 (UNFOLD_NEXT THEN SWI_EX_TAC THEN ALU_ABBREV_TAC THEN TRY PSR_ABBREV_TAC)
                    THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss) [ABS_ARM6_def,exception2num_thm]
                    THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
                    THEN ASM_SIMP_TAC (stdi_ss++BARM_ss) []
                    THEN ABBREV_TAC `alu' = SND alu` THEN UNABBREV_TAC `alu`
                    THEN ABBREV_TAC `alu1' = SND alu1` THEN UNABBREV_TAC `alu1`
                    THEN ABBREV_TAC `alu2' = SND alu2` THEN UNABBREV_TAC `alu2`
                    THEN RULE_ASSUM_TAC (SIMP_RULE (stdi_ss++ALU_ss) [])
                    THEN UNABBREV_ALL_TAC
                    THEN SIMP_TAC std_ss [DECODE_MODE_THM,CPSR_WRITE_READ]
                    THEN RW_TAC std_ss ([AC MULT_ASSOC MULT_COMM,PSR_WRITE_COMM,exception_EQ_exception,
                           num2exception_thm,exception2num_thm,
                           REWRITE_RULE [BIT_W32_NUM] DECODE_IFMODE_SET_IFMODE] @ finish_rws2),
                  UNFOLD_NEXT THEN UNDEF_TAC
                    THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss) [ABS_ARM6_def,exception2num_thm]
                    THEN STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
                    THEN ASM_SIMP_TAC (stdi_ss++BARM_ss) []
                    THEN RW_TAC std_ss finish_rws2,
                  FULL_SIMP_TAC bool_ss [DECODE_INST_NOT_UNEXEC]
                ] (* end instruction class split *)
            ] (* end unexecuted split *)
        ] (* end interrupt split *)
    ] (* end reset split *)
);

val ARM6_COR_ONE = GEN_ALL (SIMP_RULE (srw_ss()) [] ARM6_COR_LEM1);

(* -------------------------------------------------------- *)

val CORRECT_ARM6 = store_thm("CORRECT_ARM6",
  `CORRECT ARM_SPEC ARM6_SPEC IMM_ARM6 ABS_ARM6 (OSMPL OSMPL_ARM6 ARM6_SPEC IMM_ARM6) SMPL_ARM6 UNIV STRM_ARM6`,
  MATCH_MP_TAC ONE_STEP_THM
    THEN EXISTS_TAC `OSMPL_ARM6`
    THEN SIMP_TAC std_ss [STATE_ARM_THM2,STATE_ARM6_IMAP,IMM_ARM6_UNIFORM,ARM6_DATA_ABSTRACTION,
           ARM6_STREAM_ABSTRACTION,REWRITE_RULE [TCONa_def] (MATCH_MP TCON_I_THMa STATE_ARM_THM3),
           ARM6_TIME_CON_IMM,TCON_SMPL_ARM6]
    THEN REPEAT STRIP_TAC
    THEN Cases_on `x` THEN Cases_on `a` THEN Cases_on `d` THEN Cases_on `c`
    THEN FULL_SIMP_TAC (std_ss++STATE_INP_ss)
           [lem,ARM6_SPEC_STATE,ARM_SPEC_STATE,ARM6_COR_ZERO,ARM6_COR_ONE,ARM6_OUT_THM]
);

(* -------------------------------------------------------- *)

val _ = export_theory();
