(* app load ["io_onestepTheory","armTheory","simTheory"]; *)
open HolKernel boolLib Q computeLib listTheory pairTheory optionTheory
     io_onestepTheory armTheory simTheory lemmasTheory;

(* -------------------------------------------------------- *)

val SUC_RULE = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV;
fun NUMERAL_ONLY_RULE n x =
  let val y = SPEC_ALL x
  in CONJ ((GEN_ALL o simpLib.SIMP_RULE bossLib.arith_ss [] o INST [n |-> `0`]) y)
          ((GEN_ALL o INST [n |-> `NUMERAL n`]) y)
  end;

fun arm_rws () =
  let val rws = word32Lib.word_compset ()
      val _ = add_thms
     [SUC_RULE EL,HD,TL,MAP,FILTER,LENGTH,ZIP,FOLDL,
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
      FST,SND,
      SET_NZC_def,NZCV_def,CARRY_def,USER_def,mode_num_def,
      DECODE_IFMODE_SET_NZCV,DECODE_NZCV_SET_NZCV,
      DECODE_IFMODE_SET_IFMODE,DECODE_NZCV_SET_IFMODE,
      SET_NZCV_IDEM,SET_IFMODE_IDEM,SET_IFMODE_NZCV_SWP,
      DECODE_PSR_def,DECODE_PSR_THM,NUMERAL_ONLY_RULE `m` DECODE_MODE_def,mode2psr_def,
      CPSR_READ_def,CPSR_WRITE_def,
      SPSR_READ_def,SPSR_WRITE_def,
      mode_num2register_def,
      NUMERAL_ONLY_RULE `n` REG_READ_def,
      NUMERAL_ONLY_RULE `n` REG_WRITE_def,
      FETCH_PC_def,INC_PC_def,BW_READ_def,
      SIGN_EX_OFFSET_def,SHIFT_IMMEDIATE2_def,SHIFT_REGISTER2_def,
      SHIFT_IMMEDIATE_THM,SHIFT_REGISTER_THM,IMMEDIATE_def,
      ALU_multiply_def,ALU_arith_def,ALU_arith_neg_def,ALU_logic_def,SUB_def,ADD_def,
      AND_def,EOR_def,ORR_def,ALU_def,
      LSL_def,LSR_def,ASR_def,ROR_def,RRX2_def,
      ARITHMETIC_def,TEST_OR_COMP_def,ADDR_MODE1_def,
      SPLIT_WORD_def,SPLIT_WORD_THM,CONCAT_BYTES_def,UP_DOWN_def,
      DECODE_BRANCH_THM,DECODE_DATAP_THM,DECODE_MRS_THM,
      DECODE_MSR_THM,DECODE_LDR_STR_THM,DECODE_SWP_THM,
      DECODE_LDM_STM_THM,DECODE_MLA_MUL_THM,
      EXCEPTION_def,BRANCH_def,DATA_PROCESSING_def,MRS_def,MSR_def,
      LDM_STM_STATE,LDM_STM_OUT,LDR_STR_STATE,LDR_STR_OUT,SWP_STATE,SWP_OUT,
      REGISTER_LIST_THM,ADDRESS_LIST_def,LDM_LIST_def,STM_LIST_def,
      MLA_MUL_def,BORROW2_def,MSHIFT2_def,MLA_MUL_CARRY_def,MLA_MUL_DUR_EVAL2,
      NUMERAL_ONLY_RULE `n` DECODE_INST_THM,EXEC_INST_def,
      NUMERAL_ONLY_RULE `n` CONDITION_PASSED_def,CONDITION_PASSED2_def,
      IS_Dabort_def,IS_Reset_def,PROJ_Dabort_def,PROJ_Reset_def,interrupt2exception_def,
      THE_DEF,IS_SOME_DEF,IS_NONE_EQ_NONE,NOT_IS_SOME_EQ_NONE,option_case_ID,option_case_SOME_ID,
      option_case_def,SOME_11,NOT_SOME_NONE,PROJ_TRIPLE_def,interrupt2exception_def,
      NEXT_ARM_def,OUT_ARM_def
      ] rws
in
  rws
end;

val ARM_CONV = CBV_CONV (arm_rws());
val ARM_RULE = CONV_RULE ARM_CONV;
val ARM_TAC = CONV_TAC ARM_CONV;

(* -------------------------------------------------------- *)
