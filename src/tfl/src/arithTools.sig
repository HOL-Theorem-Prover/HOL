signature arithTools =
sig

type thm = Thm.thm
type term = Term.term;
type tactic = Abbrev.tactic
type conv = Abbrev.conv

  val std_thms :thm list
  val ARITH_TAC : tactic
  val ARITH : term frag list -> thm
  val ARITH_CONV : conv
end;
