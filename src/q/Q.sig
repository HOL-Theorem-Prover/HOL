signature Q =
sig
 include Abbrev

  val REFL              : term quotation -> thm
  val ABS               : term quotation -> thm -> thm
  val AC_CONV           : thm * thm -> term quotation -> thm
  val AP_TERM           : term quotation -> thm -> thm
  val AP_THM            : thm -> term quotation -> thm
  val ASM_CASES_TAC     : term quotation -> tactic
  val ASSUME            : term quotation -> thm
  val BETA_CONV         : term quotation -> thm
  val DISJ1             : thm -> term quotation -> thm
  val DISJ2             : term quotation -> thm -> thm
  val EXISTS            : term quotation * term quotation -> thm -> thm
  val EXISTS_TAC        : term quotation -> tactic
  val ID_EX_TAC         : tactic
  val REFINE_EXISTS_TAC : term quotation -> tactic
  val GEN               : term quotation -> thm -> thm
  val SPEC              : term quotation -> thm -> thm
  val ID_SPEC           : thm -> thm
  val SPECL             : term quotation list -> thm -> thm
  val ISPEC             : term quotation -> thm -> thm
  val ISPECL            : term quotation list -> thm -> thm
  val SPEC_TAC          : term quotation * term quotation -> tactic
  val ID_SPEC_TAC       : term quotation -> tactic
  val SUBGOAL_THEN      : term quotation -> thm_tactic -> tactic
  val DISCH             : term quotation -> thm -> thm
  val PAT_UNDISCH_TAC   : term quotation -> tactic
  val UNDISCH_THEN      : term quotation -> thm_tactic -> tactic
  val PAT_ASSUM         : term quotation -> thm_tactic -> tactic
  val UNDISCH_TAC       : term quotation -> tactic
  val X_CHOOSE_TAC      : term quotation -> thm_tactic
  val X_CHOOSE_THEN     : term quotation -> thm_tactic -> thm_tactic
  val X_GEN_TAC         : term quotation -> tactic
  val X_FUN_EQ_CONV     : term quotation -> conv
  val X_SKOLEM_CONV     : term quotation -> conv
  val store_thm         : string * term quotation * tactic -> thm
  val prove             : term quotation * tactic -> thm
  val ABBREV_TAC        : term quotation -> tactic
  val UNABBREV_TAC      : term quotation -> tactic
  val INST              : (term quotation,term quotation) subst -> thm -> thm
  val new_definition    : string * term quotation -> thm
  val new_infixl_definition : string * term quotation * int -> thm
  val new_infixr_definition : string * term quotation * int -> thm
  val INST_TYPE : (hol_type quotation, hol_type quotation) subst -> thm -> thm
end
