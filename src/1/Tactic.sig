signature Tactic =
sig
  include Abbrev
  datatype match_position = datatype thmpos_dtype.match_position

  val ACCEPT_TAC            : thm_tactic
  val DISCARD_TAC           : thm_tactic
  val CONTR_TAC             : thm_tactic
  val CCONTR_TAC            : tactic
  val ASSUME_TAC            : thm_tactic
  val assume_tac            : thm_tactic
  val FREEZE_THEN           : thm_tactical
  val CONJ_TAC              : tactic
  val conj_tac              : tactic
  val CONJ_ASM1_TAC         : tactic
  val conj_asm1_tac         : tactic
  val CONJ_ASM2_TAC         : tactic
  val conj_asm2_tac         : tactic
  val DISJ1_TAC             : tactic
  val disj1_tac             : tactic
  val DISJ2_TAC             : tactic
  val disj2_tac             : tactic
  val MP_TAC                : thm_tactic
  val mp_tac                : thm_tactic
  val EQ_TAC                : tactic
  val eq_tac                : tactic (* alias for EQ_TAC *)
  val iff_tac               : tactic (* alias for EQ_TAC *)
  val X_GEN_TAC             : term -> tactic
  val GEN_TAC               : tactic
  val gen_tac               : tactic
  val SPEC_TAC              : term * term -> tactic
  val ID_SPEC_TAC           : term -> tactic
  val EXISTS_TAC            : term -> tactic
  val exists_tac            : term -> tactic
  val ID_EX_TAC             : tactic
  val GSUBST_TAC            : ((term,term) Lib.subst -> term -> term)
                               -> thm list -> tactic
  val SUBST_TAC             : thm list -> tactic
  val SUBST_OCCS_TAC        : (int list * thm) list -> tactic
  val SUBST1_TAC            : thm -> tactic
  val RULE_ASSUM_TAC        : (thm -> thm) -> tactic
  val rule_assum_tac        : (thm -> thm) -> tactic
  val RULE_L_ASSUM_TAC      : (thm -> thm list) -> tactic
  val SUBST_ALL_TAC         : thm -> tactic
  val CHECK_ASSUME_TAC      : thm_tactic
  val STRIP_ASSUME_TAC      : thm_tactic
  val strip_assume_tac      : thm_tactic
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
  val disch_tac             : tactic
  val DISJ_CASES_TAC        : thm_tactic
  val CHOOSE_TAC            : thm_tactic
  val X_CHOOSE_TAC          : term -> thm_tactic
  val STRIP_TAC             : tactic
  val strip_tac             : tactic
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
  val ntac                  : int -> tactic -> tactic
  val WEAKEN_TAC            : (term -> bool) -> tactic
  val MATCH_ACCEPT_TAC      : thm -> tactic
  val MATCH_MP_TAC          : thm -> tactic
  val match_mp_tac          : thm -> tactic
  val prim_irule            : thm -> tactic
  val irule                 : thm -> tactic
  val irule_at              : match_position -> thm -> tactic
  val IRULE_TAC             : thm -> tactic
  val impl_tac              : tactic
  val impl_keep_tac         : tactic
  val HO_MATCH_ACCEPT_TAC   : thm -> tactic
  val HO_BACKCHAIN_TAC      : thm -> tactic
  val HO_MATCH_MP_TAC       : thm -> tactic
  val ho_match_mp_tac       : thm -> tactic
  val IMP_RES_TAC           : thm -> tactic
  val imp_res_tac           : thm -> tactic
  val RES_TAC               : tactic
  val res_tac               : tactic
  val provehyp              : thm_tactic
  val via                   : term * tactic -> tactic
  val CONV_TAC              : conv -> tactic
  val BETA_TAC              : tactic
  val KNOW_TAC              : term -> tactic
  val SUFF_TAC              : term -> tactic
  val suff_tac              : term -> tactic
  val TRANS_TAC             : thm -> term -> tactic

  val eliminable            : term -> bool
  val VSUBST_TAC            : thm -> tactic

  val DEEP_INTROk_TAC       : thm -> tactic -> tactic
  val DEEP_INTRO_TAC        : thm -> tactic

  val SELECT_ELIM_TAC       : tactic
  val HINT_EXISTS_TAC       : tactic
  val part_match_exists_tac : (term -> term) -> term -> tactic

  val drule                : thm_tactic
  val dxrule               : thm_tactic
  val rev_drule            : thm_tactic
  val rev_dxrule           : thm_tactic

  val drule_at             : match_position -> thm_tactic
  val dxrule_at            : match_position -> thm_tactic
  val rev_drule_at         : match_position -> thm_tactic
  val rev_dxrule_at        : match_position -> thm_tactic

  val drule_then           : thm_tactic -> thm_tactic
  val dxrule_then          : thm_tactic -> thm_tactic
  val rev_drule_then       : thm_tactic -> thm_tactic
  val rev_dxrule_then      : thm_tactic -> thm_tactic

  val drule_at_then        : match_position -> thm_tactic -> thm_tactic
  val dxrule_at_then       : match_position -> thm_tactic -> thm_tactic
  val rev_drule_at_then    : match_position -> thm_tactic -> thm_tactic
  val rev_dxrule_at_then   : match_position -> thm_tactic -> thm_tactic


  val drule_all            : thm_tactic
  val dxrule_all           : thm_tactic
  val drule_all_then       : thm_tactic -> thm_tactic
  val dxrule_all_then      : thm_tactic -> thm_tactic

  val rev_drule_all        : thm_tactic
  val rev_dxrule_all       : thm_tactic
  val rev_drule_all_then   : thm_tactic -> thm_tactic
  val rev_dxrule_all_then  : thm_tactic -> thm_tactic


  val mp_then      : match_position -> thm_tactic -> thm -> thm -> tactic
  val resolve_then : match_position -> thm_tactic -> thm -> thm -> tactic

  val export_ignore : KernelSig.kernelname -> unit
  val get_ignores : unit -> KernelSig.kernelname HOLset.set
  val unignoringc : term -> ('a -> 'b) -> ('a -> 'b)
  val unignoring : KernelSig.kernelname -> ('a -> 'b) -> ('a -> 'b)

end
