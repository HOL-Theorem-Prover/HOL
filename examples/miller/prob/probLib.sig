signature probLib =
sig
  type term = Term.term
  type thm = Thm.thm

  val SEQUENCE_CASES_TAC : term -> Abbrev.tactic
  val SEQ_CASES_TAC      : term frag list -> Abbrev.tactic

  val prob_canon_ss : simpLib.simpset

  val PROB_PSEUDO_SHD_CONV : term -> thm;
  val PROB_PSEUDO_STL_CONV : term -> thm;

  val PROB_UNIF_CONV        : term -> thm;
  val PROB_UNIFORM_CUT_CONV : term -> thm;

end
