(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

signature WeakLawsConv =
sig
  include Abbrev

  val STRONG_TO_WEAK_EQUIV_CONV		: conv -> conv

  val OE_SUM_IDEMP_CONV			: conv
  val OE_SUM_NIL_CONV			: conv
  val OE_RELAB_ELIM_CONV		: conv
  val OE_RESTR_ELIM_CONV		: conv
  val OE_PAR_ELIM_CONV			: conv
  val OE_EXP_THM_CONV			: conv
  val OE_REC_UNF_CONV			: conv

  val OE_SUM_IDEMP_TAC			: tactic
  val OE_SUM_NIL_TAC			: tactic
  val OE_RELAB_ELIM_TAC			: tactic
  val OE_RESTR_ELIM_TAC			: tactic
  val OE_PAR_ELIM_TAC			: tactic
  val OE_REC_UNF_TAC			: tactic

  val OE_RHS_RELAB_ELIM_TAC		: tactic
  val OE_EXP_THM_TAC			: tactic

  val STABLE_CONV			: conv
  val OE_SUB_CONV			: conv -> conv
  val OE_DEPTH_CONV			: conv -> conv
  val OE_TOP_DEPTH_CONV			: conv -> conv
  val OE_SUBST				: thm -> term -> thm
  val OE_LHS_SUBST1_TAC			: thm -> tactic
  val OE_LHS_SUBST_TAC			: thm list -> tactic
  val OE_RHS_SUBST1_TAC			: thm -> tactic
  val OE_RHS_SUBST_TAC			: thm list -> tactic
  val OE_SUBST1_TAC			: thm -> tactic
  val OE_SUBST_TAC			: thm list -> tactic
end
