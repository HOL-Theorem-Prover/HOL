(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

signature ObsCongrConv =
sig
  include Abbrev

  val OC_SUB_CONV			: conv -> conv
  val OC_DEPTH_CONV			: conv -> conv
  val OC_TOP_DEPTH_CONV			: conv -> conv
  val OC_SUBST				: thm -> conv
  val OC_LHS_SUBST1_TAC			: thm -> tactic
  val OC_LHS_SUBST_TAC			: thm list -> tactic
  val OC_RHS_SUBST1_TAC			: thm -> tactic
  val OC_RHS_SUBST_TAC			: thm list -> tactic
  val OC_SUBST1_TAC			: thm -> tactic
  val OC_SUBST_TAC			: thm list -> tactic

  val TAU1_CONV				: conv
  val TAU2_CONV				: conv
  val TAU3_CONV				: conv

  val STRONG_TO_OBS_CONGR_CONV		: conv -> conv
  val OC_SUM_IDEMP_CONV			: conv
  val OC_SUM_NIL_CONV			: conv
  val OC_RELAB_ELIM_CONV		: conv
  val OC_RESTR_ELIM_CONV		: conv
  val OC_PAR_ELIM_CONV			: conv
  val OC_EXP_THM_CONV			: conv
  val OC_REC_UNF_CONV			: conv

  val OC_PAR_ELIM_TAC			: tactic
  val OC_REC_UNF_TAC			: tactic
  val OC_RELAB_ELIM_TAC			: tactic
  val OC_RESTR_ELIM_TAC			: tactic
  val OC_SUM_IDEMP_TAC			: tactic
  val OC_SUM_NIL_TAC			: tactic

  val TAU1_TAC				: tactic
  val TAU2_TAC				: tactic
  val TAU3_TAC				: tactic

  val OC_RHS_RELAB_ELIM_TAC		: tactic
  val OC_EXP_THM_TAC			: tactic

end
