(* app load ["armTheory","simTheory","coreTheory"]; *)
open HolKernel boolLib bossLib Q computeLib arithmeticTheory listTheory pairTheory
     word32Theory armTheory coreTheory simTheory lemmasTheory;

(* -------------------------------------------------------- *)

val SUC_RULE = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV;
fun NUMERAL_ONLY_RULE n x =
  let val y = SPEC_ALL x
  in CONJ ((GEN_ALL o simpLib.SIMP_RULE bossLib.arith_ss [] o INST [n |-> `0`]) y)
          ((GEN_ALL o INST [n |-> `NUMERAL n`]) y)
  end;

fun arm6core_rws () =
  let val rws = word32Lib.word_compset ()
      val _ = add_thms
     [SUC_RULE EL,HD,TL,MAP,FILTER,LENGTH,
      SUC_RULE rich_listTheory.GENLIST,rich_listTheory.SNOC,
      SIMP_RULE std_ss [] REGISTER_LIST_def,
      SUC_RULE sum_numTheory.SUM_def,
      exception2mode_def,
      register_EQ_register, mode_EQ_mode, psrs_EQ_psrs, iclass_EQ_iclass, iseq_EQ_iseq,
      register2num_thm, mode2num_thm, psrs2num_thm, iclass2num_thm, iseq2num_thm, exception2num_thm,
      num2register_thm, num2condition_thm, num2exception_thm, num2iseq_thm,
      mode_case_def, condition_case_def, exception_case_def,
      SYM Sa_def,Sa_EVAL,Sb_EVAL,Sab_EQ,
      Sa_RULE4,Sb_RULE4,Sa_RULE_PSR,Sb_RULE_PSR,
      FST,SND,INC_IS,

      ONECOMP_def,CLEARBIT_def,NUMERAL_LEASTBIT,
      NMREQ_def,PCWA_def,
      NBW_def,NOPC_def,NRW_def,AREG_def,
      DIN_def,DINWRITE_def,MASK_def,
      NBS_def,RP_def,PENCZ_def,OFFSET_def,FIELD_def,RBA_def,RAA_def,PSRA_def,
        BUSB_def,BUSA_def,SHIFTER_def,BORROW_def,COUNT1_def,MUL1_def,MULZ_def,
        MULX_def,PSRFBWRITE_def,SCTRLREGWRITE_def,ALUAWRITE_def,ALUBWRITE_def,
        BASELATCH_def,NCPI_def,RWA_def,
      ALU6_def,MSHIFT,PSRWA_def,PSRDAT_def,
      ABORTINST_def,DATAABT_def,IC_def,IS_def,COPROC1_def,DATAABT1_def,FIQACT_def,
        IRQACT_def,PCCHANGE_def,RESETLATCH_def,RESETSTART_def,INTSEQ_def,NEWINST_def,
        PIPEALL_def,PIPEBLL_def,PIPECWRITE_def,
      NXTIC_def,INC_IS_def,NXTIS_def,PIPEAWRITE_def,PIPEBWRITE_def,PIPESTATAWRITE_def,
        PIPESTATBWRITE_def,PIPESTATIREGWRITE_def,PIPEAVAL_def,IREGVAL_def,PIPEAABT_def,
        IREGABT2_def,AREGN1_def,ENDINST_def,

      SET_NZC_def,NZCV_def,USER_def,mode_num_def,
      DECODE_IFMODE_SET_NZCV,DECODE_NZCV_SET_NZCV,
      DECODE_IFMODE_SET_IFMODE,DECODE_NZCV_SET_IFMODE,
      SET_NZCV_IDEM,SET_IFMODE_IDEM,SET_IFMODE_NZCV_SWP,
      DECODE_PSR_def,NUMERAL_ONLY_RULE `m` DECODE_MODE_def,DECODE_PSR_THM,mode2psr_def,
      CPSR_READ_def,CPSR_WRITE_def,
      SPSR_READ_def,SPSR_WRITE_def,
      mode_num2register_def,NUMERAL_ONLY_RULE `n` REG_READ_def,
      NUMERAL_ONLY_RULE `n` REG_WRITE_def,INC_PC_def,
      FETCH_PC_def,REG_READ6_def,
      SIGN_EX_OFFSET_def,
(* SHIFT_IMMEDIATE2_def,SHIFT_REGISTER2_def,ADDR_MODE2_def,UP_DOWN_def *)
      ALU_arith_def,ALU_arith_neg_def,ALU_logic_def,SUB_def,ADD_def,
      AND_def,EOR_def,ORR_def, ALU_def,
      LSL_def,LSR_def,ASR_def,ROR_def,RRX_def,

      NUMERAL_ONLY_RULE `n` CONDITION_PASSED_def,CONDITION_PASSED2_def,NUMERAL_ONLY_RULE `n` DECODE_INST_THM,
      PROJ_NRESET_def,PROJ_ABORT_def,IS_RESET_def,IS_ABORT_def,
      MLA_MUL_DUR_EVAL2,DUR_IC_def,
      INIT_ARM6_def,NEXT_ARM6_def,OUT_ARM6_def,CONJUNCT1 STATE_ARM6_def
      ] rws
in
  rws
end;

val ARM6_CONV = CBV_CONV (arm6core_rws());
val ARM6_RULE = CONV_RULE ARM6_CONV;
val ARM6_TAC = CONV_TAC ARM6_CONV;

(* -------------------------------------------------------- *)
