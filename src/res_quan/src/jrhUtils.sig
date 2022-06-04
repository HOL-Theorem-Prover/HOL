signature jrhUtils =
sig
type term = Term.term
type thm = Thm.thm
type tactic = Abbrev.tactic

  val HALF_MK_ABS : thm -> thm
  val TAUT_CONV : term -> thm
  val AC : thm * thm -> term -> thm
  val GEN_PAIR_TAC : tactic
  val MK_COMB_TAC  : tactic
  val BINOP_TAC    : tactic
  val SYM_CANON_CONV : thm -> (term * term -> bool) -> (term -> thm)
  val IMP_SUBST_TAC : thm -> tactic
  val ABBREV_TAC : term -> tactic
  val EXT_CONV : term -> thm
  val ABS_TAC : tactic
  val EQUAL_TAC : tactic
  val X_BETA_CONV : term -> term -> thm
  val EXACT_CONV : thm list -> (term -> thm)
  val HABS_CONV : term -> thm
  val EXPAND_TAC : string -> tactic
  val GEN_REWR_TAC : ((term -> thm) -> term -> thm) -> thm list -> tactic
end
