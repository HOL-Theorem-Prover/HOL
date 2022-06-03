signature jrhUtils =
sig
  include Abbrev

  val HALF_MK_ABS : thm -> thm
  val TAUT_CONV : conv
  val AC : thm * thm -> conv
  val GEN_PAIR_TAC : tactic
  val MK_COMB_TAC  : tactic
  val BINOP_TAC    : tactic
  val SYM_CANON_CONV : thm -> (term * term -> bool) -> conv
  val IMP_SUBST_TAC : thm_tactic
  val ABBREV_TAC : term -> tactic
  val EXT_CONV : conv
  val ABS_TAC : tactic
  val EQUAL_TAC : tactic
  val X_BETA_CONV : term -> conv
  val EXACT_CONV : thm list -> conv
  val HABS_CONV : conv
  val EXPAND_TAC : string -> tactic
  val GEN_REWR_TAC : (conv -> conv) -> thm list -> tactic

  val NUM_EQ_CONV : conv
end
