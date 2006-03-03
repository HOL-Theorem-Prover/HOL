structure modelsLib :> modelsLib =
struct

(* interactive use:
  app load ["pred_setSimps", "io_onestepTheory", "armTheory", "wordsLib",
            "coreTheory", "simTheory", "instructionTheory"];
*)

open HolKernel boolLib bossLib;
open Q computeLib listTheory pairTheory optionTheory wordsTheory;
open io_onestepTheory armTheory coreTheory simTheory lemmasTheory;
open instructionTheory;

(* ------------------------------------------------------------------------- *)

val SUC_RULE = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV;

fun NUM_ONLY_RULE n x =
  let val y = SPEC_ALL x
  in CONJ
      ((GEN_ALL o INST [n |-> `0`]) y)
      ((GEN_ALL o INST [n |-> `NUMERAL n`]) y)
  end;

fun WORD_ONLY_RULE n x =
  let val y = SPEC_ALL x
  in CONJ
      ((GEN_ALL o CONV_RULE (RHS_CONV EVAL_CONV) o INST [n |-> `0w`]) y)
      ((GEN_ALL o INST [n |-> `n2w (NUMERAL n)`]) y)
  end;

val EXTRACT_RULE1 = SIMP_RULE std_ss [w2w_def,word_extract_def];
val EXTRACT_RULE2 = CONV_RULE (CBV_CONV (wordsLib.words_compset()));

val common_thms =
  [FST,SND,SUC_RULE EL,HD,TL,MAP,FILTER,LENGTH,ZIP,FOLDL,
   SUC_RULE rich_listTheory.GENLIST,rich_listTheory.SNOC,
   SUC_RULE rich_listTheory.FIRSTN,combinTheory.K_THM,
   register_EQ_register,num2register_thm,register2num_thm,
   mode_EQ_mode,mode2num_thm,mode_case_def,
   psrs_EQ_psrs,psrs2num_thm,
   iclass_EQ_iclass,iclass2num_thm,
   exception_EQ_exception,exception2num_thm,exception_case_def,
   num2exception_thm,exception2mode_def,
   num2condition_thm,condition2num_thm,condition_case_def,
   interrupts_case_def,
   SUBST_EVAL,

   SET_NZC_def,NZCV_def,USER_def,INC_IS,INC_IS_def,mode_num_def,
   EXTRACT_RULE1 DECODE_IFMODE_SET_NZCV,DECODE_NZCV_SET_NZCV,
   EXTRACT_RULE1 DECODE_IFMODE_SET_IFMODE,DECODE_NZCV_SET_IFMODE,
   SET_NZCV_IDEM,SET_IFMODE_IDEM,SET_IFMODE_NZCV_SWP,
   DECODE_PSR_def,DECODE_MODE_def,DECODE_PSR_THM,
   CPSR_READ_def,CPSR_WRITE_def,SPSR_READ_def,SPSR_WRITE_def,
   CPSR_WRITE_n2w,SPSR_WRITE_n2w,mode_reg2num_def,mode2psr_def,
   REG_READ_def,REG_WRITE_def,INC_PC_def,FETCH_PC_def,REG_READ6_def,
   word_modify_PSR,word_modify_PSR2,
   ALU_arith_def,ALU_arith_neg_def,ALU_logic_def,SUB_def,ADD_def,
   AND_def,EOR_def,ORR_def,ALU_def,
   LSL_def,LSR_def,ASR_def,ROR_def,
   WORD_ONLY_RULE `ireg` CONDITION_PASSED_def,CONDITION_PASSED2_def,
   DECODE_INST_THM,MLA_MUL_DUR_n2w];

fun arm_compset () =
  let val compset = wordsLib.words_compset ()
      val thms = common_thms @
       [ZIP,FOLDL,
        state_inp_accessors, state_inp_updates_eq_literal,
        state_inp_accfupds, state_inp_fupdfupds, state_inp_literal_11,
        state_inp_fupdfupds_comp, state_inp_fupdcanon,
        state_inp_fupdcanon_comp,
        state_out_accessors, state_out_updates_eq_literal,
        state_out_accfupds, state_out_fupdfupds, state_out_literal_11,
        state_out_fupdfupds_comp, state_out_fupdcanon,
        state_out_fupdcanon_comp,
        transfer_options_accessors, transfer_options_updates_eq_literal,
        transfer_options_accfupds, transfer_options_fupdfupds,
        transfer_options_literal_11, transfer_options_fupdfupds_comp,
        transfer_options_fupdcanon, transfer_options_fupdcanon_comp,
        state_arm_case_def,shift_case_def,

        DECODE_BRANCH_THM,DECODE_DATAP_THM,DECODE_MRS_THM,
        DECODE_MSR_THM,DECODE_LDR_STR_THM,DECODE_SWP_THM,
        DECODE_LDM_STM_THM,DECODE_MLA_MUL_THM,DECODE_LDC_STC_THM,
        DECODE_PSRD_def, CONDITION_PASSED3_def,

   cond_pass_enc_br, cond_pass_enc_coproc, cond_pass_enc_swp,
   cond_pass_enc_data_proc, cond_pass_enc_data_proc2, cond_pass_enc_data_proc3,
   cond_pass_enc_ldm_stm, cond_pass_enc_ldr_str, cond_pass_enc_mla_mul,
   cond_pass_enc_mrs, cond_pass_enc_msr, cond_pass_enc_swi,

   decode_enc_br, decode_enc_coproc, decode_enc_swp,
   decode_enc_data_proc, decode_enc_data_proc2, decode_enc_data_proc3,
   decode_enc_reg_shift, decode_enc_reg_shift2, decode_enc_reg_shift3,
   decode_enc_ldm_stm, decode_enc_ldr_str, decode_enc_mla_mul,
   decode_enc_mrs, decode_enc_msr, decode_enc_swi,

   decode_br_enc, decode_ldc_stc_enc, decode_mrc_enc,
   decode_data_proc_enc, decode_data_proc_enc2, decode_data_proc_enc3,
   decode_ldm_stm_enc, decode_ldr_str_enc, decode_mla_mul_enc,
   decode_mrs_enc, decode_msr_enc, decode_swp_enc,

   EXTRACT_RULE2 immediate_enc, EXTRACT_RULE2 immediate_enc2,
   EXTRACT_RULE2 shift_immediate_enc, EXTRACT_RULE2 shift_immediate_enc2,
   EXTRACT_RULE2 shift_immediate_shift_register, EXTRACT_RULE2 shift_register_enc,

        CARRY_def,BW_READ_def,
        SHIFT_IMMEDIATE2_def,SHIFT_REGISTER2_def,
        NUM_ONLY_RULE `opnd2` SHIFT_IMMEDIATE_THM,
        NUM_ONLY_RULE `opnd2` SHIFT_REGISTER_THM,
        WORD_ONLY_RULE `opnd2` IMMEDIATE_def,
        ALU_multiply_def,ARITHMETIC_def,TEST_OR_COMP_def,UP_DOWN_def,
        ADDR_MODE1_def,ADDR_MODE2_def,ADDR_MODE4_def,ADDR_MODE5_def,
        REGISTER_LIST_THM,ADDRESS_LIST_def,FIRST_ADDRESS_def,WB_ADDRESS_def,
        LDM_LIST_def,STM_LIST_def,BORROW2_def,MSHIFT2_def,MLA_MUL_CARRY_def,

        EXCEPTION_def,BRANCH_def,DATA_PROCESSING_def,MRS_def,LDR_STR_def,
        MLA_MUL_def,SWP_def,MRC_def,MCR_OUT_def,MSR_def,LDM_STM_def,LDC_STC_def,

        SIMP_RULE (std_ss++pred_setSimps.PRED_SET_ss) []
          interrupt2exception_def,
        IS_Dabort_def,IS_Reset_def,PROJ_Dabort_def,PROJ_Reset_def,
        THE_DEF,IS_SOME_DEF,IS_NONE_EQ_NONE,NOT_IS_SOME_EQ_NONE,
        option_case_ID,option_case_SOME_ID,
        option_case_def,SOME_11,NOT_SOME_NONE,PROJ_IF_FLAGS_def,
        EXEC_INST_def,NEXT_ARM_def,OUT_ARM_def]
       val _ = add_thms thms compset
in
  compset
end;

fun arm6_compset () =
  let val compset = wordsLib.words_compset ()
      val thms = common_thms @
       [SIMP_RULE std_ss [] REGISTER_LIST_def,SUC_RULE sum_numTheory.SUM_def,
        iseq_EQ_iseq, iseq2num_thm, num2iseq_thm,

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
        NXTIC_def,NXTIS_def,PIPEAWRITE_def,PIPEBWRITE_def,
        PIPESTATAWRITE_def,PIPESTATBWRITE_def,PIPESTATIREGWRITE_def,
        PIPEAVAL_def,IREGVAL_def,PIPEAABT_def,
        IREGABT2_def,AREGN1_def,ENDINST_def,

        PROJ_NRESET_def,PROJ_ABORT_def,IS_RESET_def,IS_ABORT_def,DUR_IC_def,
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
