signature RealArith =
sig
   type term = Term.term
   type thm = Thm.thm
   type tactic = Abbrev.tactic

  val PURE_REAL_ARITH_TAC : tactic
  val REAL_ARITH_TAC      : tactic
  val REAL_ARITH          : term -> thm
end
