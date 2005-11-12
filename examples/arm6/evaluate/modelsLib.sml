structure modelsLib :> modelsLib =
struct

(* interactive use:
  app load ["pred_setSimps", "io_onestepTheory", "armTheory",
            "coreThoery", "simTheory"];
*)

open HolKernel boolLib bossLib;
open Q computeLib listTheory pairTheory optionTheory wordsTheory;
open io_onestepTheory armTheory coreTheory simTheory lemmasTheory;

(* ------------------------------------------------------------------------- *)

val SUC_RULE = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV;

fun NUMERAL_ONLY_RULE n x =
  let val y = SPEC_ALL x
  in CONJ
      ((GEN_ALL o simpLib.SIMP_RULE bossLib.arith_ss [] o INST [n |-> `0`]) y)
      ((GEN_ALL o INST [n |-> `NUMERAL n`]) y)
  end;

val EXTRACT_RULE = SIMP_RULE std_ss [w2w_def,word_extract_def];

fun arm_compset () =
  let val compset = wordsLib.words_compset ()
      val thms =
       [FST,SND,SUC_RULE EL,HD,TL,MAP,FILTER,LENGTH,ZIP,FOLDL,
        SUC_RULE rich_listTheory.GENLIST,rich_listTheory.SNOC,
        SUC_RULE rich_listTheory.FIRSTN,combinTheory.K_THM,
        state_inp_accessors, state_inp_updates_eq_literal,
        state_inp_accfupds, state_inp_fupdfupds, state_inp_literal_11,
        state_inp_fupdfupds_comp, state_inp_fupdcanon,
        state_inp_fupdcanon_comp,
        state_out_accessors, state_out_updates_eq_literal,
        state_out_accfupds, state_out_fupdfupds, state_out_literal_11,
        state_out_fupdfupds_comp, state_out_fupdcanon,
        state_out_fupdcanon_comp,
        register_EQ_register,num2register_thm,register2num_thm,
        mode_EQ_mode,mode2num_thm,
        psrs_EQ_psrs,psrs2num_thm,
        iclass_EQ_iclass,iclass2num_thm,
        exception_EQ_exception,num2exception_thm,
        exception2num_thm,exception2mode_def,
        num2condition_thm,condition2num_thm,
        mode_case_def,condition_case_def,
        exception_case_def,interrupts_case_def,
        SYM Sa_def,Sa_EVAL,Sb_EVAL,Sab_EQ,
        Sa_RULE4,Sb_RULE4,
        Sa_RULE_PSR,Sb_RULE_PSR,
        DECODE_BRANCH_THM,DECODE_DATAP_THM,DECODE_MRS_THM,
        DECODE_MSR_THM,DECODE_LDR_STR_THM,DECODE_SWP_THM,
        DECODE_LDM_STM_THM,DECODE_MLA_MUL_THM,DECODE_LDC_STC_THM,
        CARRY_def,USER_def,mode_num_def,SET_NZC_def,NZCV_def,
        EXTRACT_RULE DECODE_IFMODE_SET_NZCV,DECODE_NZCV_SET_NZCV,
        EXTRACT_RULE DECODE_IFMODE_SET_IFMODE,DECODE_NZCV_SET_IFMODE,
        SET_NZCV_IDEM,SET_IFMODE_IDEM,SET_IFMODE_NZCV_SWP,
        DECODE_PSR_def,DECODE_PSR_THM,DECODE_MODE_def,
        CPSR_READ_def,CPSR_WRITE_def,SPSR_READ_def,SPSR_WRITE_def,
        mode2psr_def,mode_reg2num_def,
        REG_READ_def,REG_WRITE_def,FETCH_PC_def,INC_PC_def,BW_READ_def,
        SHIFT_IMMEDIATE2_def,SHIFT_REGISTER2_def,
        SHIFT_IMMEDIATE_THM,SHIFT_REGISTER_THM,IMMEDIATE_def,
        ALU_multiply_def,ALU_arith_def,ALU_arith_neg_def,ALU_logic_def,
        SUB_def,ADD_def,AND_def,EOR_def,ORR_def,
        LSL_def,LSR_def,ASR_def,ROR_def,RRX2_def,
        ALU_def,ARITHMETIC_def,TEST_OR_COMP_def,UP_DOWN_def,
        ADDR_MODE1_def,ADDR_MODE2_def,ADDR_MODE4_def,ADDR_MODE5_def,
        EXCEPTION_def,BRANCH_def,DATA_PROCESSING_def,MRS_def,LDR_STR_def,
        MLA_MUL_def,SWP_def,MRC_def,MCR_OUT_def,MSR_def,LDM_STM_def,LDC_STC_def,
        REGISTER_LIST_THM,ADDRESS_LIST_def,LDM_LIST_def,STM_LIST_def,
        BORROW2_def,MSHIFT2_def,MLA_MUL_CARRY_def,MLA_MUL_DUR_n2w,
        NUMERAL_ONLY_RULE `n` DECODE_INST_THM,EXEC_INST_def,
        CONDITION_PASSED_def,CONDITION_PASSED2_def,
        SIMP_RULE (std_ss++pred_setSimps.PRED_SET_ss) []
          interrupt2exception_def,
        IS_Dabort_def,IS_Reset_def,PROJ_Dabort_def,PROJ_Reset_def,
        THE_DEF,IS_SOME_DEF,IS_NONE_EQ_NONE,NOT_IS_SOME_EQ_NONE,
        option_case_ID,option_case_SOME_ID,
        option_case_def,SOME_11,NOT_SOME_NONE,PROJ_IF_FLAGS_def,
        NEXT_ARM_def,OUT_ARM_def]
       val _ = add_thms thms compset
in
  compset
end;

fun arm6_compset () =
  let val compset = wordsLib.words_compset ()
      val thms =
       [SUC_RULE EL,HD,TL,MAP,FILTER,LENGTH,
        SUC_RULE rich_listTheory.GENLIST,rich_listTheory.SNOC,
        SIMP_RULE std_ss [] REGISTER_LIST_def,
        SUC_RULE sum_numTheory.SUM_def,
        exception2mode_def,
        register_EQ_register,mode_EQ_mode,psrs_EQ_psrs,
        iclass_EQ_iclass,iseq_EQ_iseq,
        register2num_thm,mode2num_thm,psrs2num_thm,iclass2num_thm,
        iseq2num_thm, exception2num_thm,
        num2register_thm, num2condition_thm, num2exception_thm, num2iseq_thm,
        mode_case_def, condition_case_def, exception_case_def,
        SYM Sa_def,Sa_EVAL,Sb_EVAL,Sab_EQ,
        Sa_RULE4,Sb_RULE4,Sa_RULE_PSR,Sb_RULE_PSR,
        FST,SND,INC_IS,

        CLEARBIT_def,NUMERAL_LEASTBIT16,
        NMREQ_def,PCWA_def,
        NBW_def,NOPC_def,NRW_def,AREG_def,
        DIN_def,DINWRITE_def,MASK_def,
        NBS_def,RP_def,PENCZ_def,OFFSET_def,FIELD_def,RBA_def,RAA_def,PSRA_def,
        BUSB_def,BUSA_def,SHIFTER_def,BORROW_def,COUNT1_def,MUL1_def,MULZ_def,
        MULX_def,PSRFBWRITE_def,SCTRLREGWRITE_def,ALUAWRITE_def,ALUBWRITE_def,
        BASELATCH_def,NCPI_def,RWA_def,
        ALU6_def,MSHIFT,PSRWA_def,PSRDAT_def,
        ABORTINST_def,DATAABT_def,IC_def,IS_def,COPROC1_def,DATAABT1_def,
        FIQACT_def,IRQACT_def,PCCHANGE_def,RESETLATCH_def,RESETSTART_def,
        INTSEQ_def,NEWINST_def,PIPEALL_def,PIPEBLL_def,PIPECWRITE_def,
        NXTIC_def,INC_IS_def,NXTIS_def,PIPEAWRITE_def,PIPEBWRITE_def,
        PIPESTATAWRITE_def,PIPESTATBWRITE_def,PIPESTATIREGWRITE_def,
        PIPEAVAL_def,IREGVAL_def,PIPEAABT_def,
        IREGABT2_def,AREGN1_def,ENDINST_def,

        SET_NZC_def,NZCV_def,USER_def,mode_num_def,
        EXTRACT_RULE DECODE_IFMODE_SET_NZCV,DECODE_NZCV_SET_NZCV,
        EXTRACT_RULE DECODE_IFMODE_SET_IFMODE,DECODE_NZCV_SET_IFMODE,
        SET_NZCV_IDEM,SET_IFMODE_IDEM,SET_IFMODE_NZCV_SWP,
        DECODE_PSR_def,DECODE_MODE_def,DECODE_PSR_THM,
        CPSR_READ_def,CPSR_WRITE_def,
        SPSR_READ_def,SPSR_WRITE_def,
        mode_reg2num_def,mode2psr_def,
        REG_READ_def,REG_WRITE_def,INC_PC_def,FETCH_PC_def,REG_READ6_def,
        ALU_arith_def,ALU_arith_neg_def,ALU_logic_def,SUB_def,ADD_def,
        AND_def,EOR_def,ORR_def,ALU_def,
        LSL_def,LSR_def,ASR_def,ROR_def,RRX2_def,

        CONDITION_PASSED_def,CONDITION_PASSED2_def,
        NUMERAL_ONLY_RULE `n` DECODE_INST_THM,
        PROJ_NRESET_def,PROJ_ABORT_def,IS_RESET_def,IS_ABORT_def,
        MLA_MUL_DUR_n2w,DUR_IC_def,
        INIT_ARM6_def,NEXT_ARM6_def,OUT_ARM6_def,CONJUNCT1 STATE_ARM6_def]
      val _ = add_thms thms compset
in
  compset
end;

val ARM_CONV  = CBV_CONV (arm_compset());
val ARM_RULE  = CONV_RULE ARM_CONV;
val ARM6_CONV = CBV_CONV (arm6_compset());
val ARM6_RULE = CONV_RULE ARM6_CONV;

end
