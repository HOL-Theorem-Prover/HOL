(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

signature StrongLawsConv =
sig
  include Abbrev

  val STRONG_SUM_ASSOC_CONV     : conv
  val STRONG_SUM_NIL_CONV       : conv
  val STRONG_FIND_IDEMP         : term -> term list -> thm
  val STRONG_SUM_IDEMP_CONV     : conv
  val STRONG_RESTR_ELIM_CONV    : conv
  val STRONG_RELAB_ELIM_CONV    : conv
  val COND_EVAL_CONV            : conv
  val BETA_COND_CONV            : conv
  val IS_PREFIX_CHECK           : term -> term -> term -> thm
  val STRONG_PAR_NIL_CONV       : conv
  val STRONG_NIL_SUM_PAR_CONV   : conv
  val PREFIX_EXTRACT            : conv
  val SIMPLIFY_CONV             : conv
  val ALL_SYNC_CONV             : term -> term -> term -> term -> thm
  val STRONG_PAR_SUM_CONV       : conv
  val STRONG_PAR_PREFIX_CONV    : term * term -> term * term -> thm
  val STRONG_PAR_ELIM_CONV      : conv
  val STRONG_EXP_THM_CONV       : conv
  val STRONG_REC_UNF_CONV       : conv
  val STRONG_REC_FOLD_CONV      : conv
  val STRONG_PAR_ELIM_TAC       : tactic
  val STRONG_REC_UNF_TAC        : tactic
  val STRONG_RELAB_ELIM_TAC     : tactic
  val STRONG_RESTR_ELIM_TAC     : tactic
  val STRONG_SUM_IDEMP_TAC      : tactic
  val STRONG_SUM_NIL_TAC        : tactic
  val STRONG_EXP_THM_TAC        : tactic

end
