signature Q =
sig
  include Abbrev
  type tmquote = term quotation
  type tyquote = hol_type quotation

  val REFL                  : tmquote -> thm
  val ABS                   : tmquote -> thm -> thm
  val AC_CONV               : thm * thm -> tmquote -> thm
  val AP_TERM               : tmquote -> thm -> thm
  val AP_THM                : thm -> tmquote -> thm
  val ASM_CASES_TAC         : tmquote -> tactic
  val ASSUME                : tmquote -> thm
  val BETA_CONV             : tmquote -> thm
  val DISJ1                 : thm -> tmquote -> thm
  val DISJ2                 : tmquote -> thm -> thm
  val EXISTS                : tmquote * tmquote -> thm -> thm
  val EXISTS_TAC            : tmquote -> tactic
  val ID_EX_TAC             : tactic
  val REFINE_EXISTS_TAC     : tmquote -> tactic
  val GEN                   : tmquote -> thm -> thm
  val SPEC                  : tmquote -> thm -> thm
  val ID_SPEC               : thm -> thm
  val SPECL                 : tmquote list -> thm -> thm
  val ISPEC                 : tmquote -> thm -> thm
  val ISPECL                : tmquote list -> thm -> thm
  val SPEC_TAC              : tmquote * tmquote -> tactic
  val SPEC_THEN             : tmquote -> thm_tactic -> thm -> tactic
  val SPECL_THEN            : tmquote list -> thm_tactic -> thm -> tactic
  val ISPEC_THEN            : tmquote -> thm_tactic -> thm -> tactic
  val ISPECL_THEN           : tmquote list -> thm_tactic -> thm ->tactic
  val ID_SPEC_TAC           : tmquote -> tactic
  val SUBGOAL_THEN          : tmquote -> thm_tactic -> tactic
  val DISCH                 : tmquote -> thm -> thm
  val PAT_UNDISCH_TAC       : tmquote -> tactic
  val UNDISCH_THEN          : tmquote -> thm_tactic -> tactic
  val PAT_ASSUM             : tmquote -> thm_tactic -> tactic
  val UNDISCH_TAC           : tmquote -> tactic
  val X_CHOOSE_TAC          : tmquote -> thm_tactic
  val X_CHOOSE_THEN         : tmquote -> thm_tactic -> thm_tactic
  val X_GEN_TAC             : tmquote -> tactic
  val X_FUN_EQ_CONV         : tmquote -> conv
  val X_SKOLEM_CONV         : tmquote -> conv
  val store_thm             : string * tmquote * tactic -> thm
  val prove                 : tmquote * tactic -> thm
  val INST                  : (tmquote, tmquote) subst -> thm -> thm
  val new_definition        : string * tmquote -> thm
  val new_infixl_definition : string * tmquote * int -> thm
  val new_infixr_definition : string * tmquote * int -> thm
  val INST_TYPE             : (tyquote, tyquote) subst -> thm -> thm

  val ABBREV_TAC            : tmquote -> tactic
  val PAT_ABBREV_TAC        : tmquote -> tactic
  val MATCH_ABBREV_TAC      : tmquote -> tactic
  val HO_MATCH_ABBREV_TAC   : tmquote -> tactic
  val UNABBREV_TAC          : tmquote -> tactic
  val RM_ABBREV_TAC         : tmquote -> tactic

end
