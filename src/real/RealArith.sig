signature RealArith =
sig
   type term = Term.term
   type thm = Thm.thm
   type tactic = Abbrev.tactic

  val PURE_REAL_ARITH_TAC : tactic

  val REAL_ARITH_TAC      : tactic
  val REAL_ASM_ARITH_TAC  : tactic

 (* PURE_REAL_ARITH_TAC doesn't throw away assumptions, but requires
    them to be pre-normalised in order to work.  There also must not
    be any non-Presburger terms lurking amongst them.

    REAL_ASM_ARITH_TAC moves all assumptions into the goal, and then
    proceeds.  It thus gets around the two restrictions above.  *)

  val REAL_ARITH          : term -> thm
end
