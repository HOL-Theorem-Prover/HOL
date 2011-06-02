signature Tactic =
sig
  include Abbrev

  val ACCEPT_TAC            : thm_tactic
  val DISCARD_TAC           : thm -> tactic
  val CONTR_TAC             : thm_tactic
  val CCONTR_TAC            : tactic
  val ASSUME_TAC            : thm_tactic
  val FREEZE_THEN           : thm_tactical
  val CONJ_TAC              : tactic
  val CONJ_ASM1_TAC         : tactic
  val CONJ_ASM2_TAC         : tactic
  val DISJ1_TAC             : tactic
  val DISJ2_TAC             : tactic
  val MP_TAC                : thm_tactic
  val EQ_TAC                : tactic
  val X_GEN_TAC             : term -> tactic
  val GEN_TAC               : tactic
  val SPEC_TAC              : term * term -> tactic
  val ID_SPEC_TAC           : term -> tactic
  val EXISTS_TAC            : term -> tactic
  val GSUBST_TAC            : ((term,term) Lib.subst -> term -> term)
                               -> thm list -> tactic
  val SUBST_TAC             : thm list -> tactic
  val SUBST_OCCS_TAC        : (int list * thm) list -> tactic
  val SUBST1_TAC            : thm -> tactic
  val RULE_ASSUM_TAC        : (thm -> thm) -> tactic
  val SUBST_ALL_TAC         : thm -> tactic
  val CHECK_ASSUME_TAC      : thm_tactic
  val STRIP_ASSUME_TAC      : thm_tactic
  val STRUCT_CASES_TAC      : thm_tactic
  val FULL_STRUCT_CASES_TAC : thm_tactic
  val GEN_COND_CASES_TAC    : (term -> bool) -> tactic
  val COND_CASES_TAC        : tactic
  val IF_CASES_TAC          : tactic
  val BOOL_CASES_TAC        : term -> tactic
  val STRIP_GOAL_THEN       : thm_tactic -> tactic
  val FILTER_GEN_TAC        : term -> tactic
  val FILTER_DISCH_THEN     : thm_tactic -> term -> tactic
  val FILTER_STRIP_THEN     : thm_tactic -> term -> tactic
  val DISCH_TAC             : tactic
  val DISJ_CASES_TAC        : thm_tactic
  val CHOOSE_TAC            : thm_tactic
  val X_CHOOSE_TAC          : term -> thm_tactic
  val STRIP_TAC             : tactic
  val FILTER_DISCH_TAC      : term -> tactic
  val FILTER_STRIP_TAC      : term -> tactic
  val ASM_CASES_TAC         : term -> tactic
  val REFL_TAC              : tactic
  val UNDISCH_TAC           : term -> tactic
  val AP_TERM_TAC           : tactic
  val AP_THM_TAC            : tactic
  val MK_COMB_TAC           : tactic
  val BINOP_TAC             : tactic
  val ABS_TAC               : tactic
  val NTAC                  : int -> tactic -> tactic
  val WEAKEN_TAC            : (term -> bool) -> tactic
  val MATCH_ACCEPT_TAC      : thm -> tactic
  val MATCH_MP_TAC          : thm -> tactic
  val HO_MATCH_ACCEPT_TAC   : thm -> tactic
  val HO_BACKCHAIN_TAC      : thm -> tactic
  val HO_MATCH_MP_TAC       : thm -> tactic
  val IMP_RES_TAC           : thm -> tactic
  val RES_TAC               : tactic
  val via                   : term * tactic -> tactic
  val CONV_TAC              : conv -> tactic
  val BETA_TAC              : tactic
  val KNOW_TAC              : term -> tactic
  val SUFF_TAC              : term -> tactic

  val DEEP_INTROk_TAC       : thm -> tactic -> tactic
  val DEEP_INTRO_TAC        : thm -> tactic

  val SELECT_ELIM_TAC       : tactic
end;
