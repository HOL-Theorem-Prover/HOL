signature Cooper =
sig
  type term = Term.term
  type thm = Thm.thm
  type conv = Abbrev.conv
  type tactic = Abbrev.tactic

  val COOPER_CONV                 : conv
  val COOPER_PROVE                : conv
  val COOPER_TAC                  : tactic
  val is_presburger               : term -> bool
  val non_presburger_subterms     : term -> term list
  val decide_pure_presburger_term : term -> thm
end
