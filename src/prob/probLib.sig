signature probLib =
sig
  type term = Term.term
  type thm = Thm.thm

  val SEQ_CASES_TAC : term frag list -> Abbrev.tactic

  val prob_canon_ss : simpLib.simpset

  val SHD_PSEUDO_CONV : term -> thm
  val STL_PSEUDO_CONV : term -> thm

  val UNIFORM_CONV    : term -> thm

end
