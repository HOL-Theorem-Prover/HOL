signature  iclass_compLib =
sig
  include Abbrev

  val BARM_ss : simpLib.ssfrag
  val ALU_ss : simpLib.ssfrag
  val Cases_on_arm6inp : term frag list -> tactic
  val Cases_on_arm6 : term frag list -> tactic
  val Cases_arm6 : tactic
  val UNEXEC_ss : simpLib.ssfrag
  val SWP_ss : simpLib.ssfrag
  val MRS_MSR_ss : simpLib.ssfrag
  val DATA_PROC_ss : simpLib.ssfrag
  val REG_SHIFT_ss : simpLib.ssfrag
  val LDR_ss : simpLib.ssfrag
  val STR_ss : simpLib.ssfrag
  val BR_ss : simpLib.ssfrag
  val SWI_EX_ss : simpLib.ssfrag
  val CDP_UND_ss : simpLib.ssfrag
  val MRC_ss : simpLib.ssfrag
  val MCR_ss : simpLib.ssfrag
  val LDC_ss : simpLib.ssfrag
  val STC_ss : simpLib.ssfrag
  val LDM_ss : simpLib.ssfrag
  val STM_ss : simpLib.ssfrag
  val MLA_MUL_ss : simpLib.ssfrag
  val UNEXEC_TAC : tactic
  val SWP_TAC : tactic
  val MRS_MSR_TAC : tactic
  val DATA_PROC_TAC : tactic
  val REG_SHIFT_TAC : tactic
  val LDR_TAC : tactic
  val STR_TAC : tactic
  val BR_TAC : tactic
  val SWI_EX_TAC : tactic
  val CDP_UND_TAC : tactic
  val MRC_TAC : tactic
  val MCR_TAC : tactic
  val LDC_TAC : tactic
  val STC_TAC : tactic
  val LDM_TAC : tactic
  val STM_TAC : tactic
  val MLA_MUL_TAC : tactic
  val LDM_ITER_CONV : conv
  val STM_ITER_CONV : conv
  val MLA_MUL_CONV : conv
end
