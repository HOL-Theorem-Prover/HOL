signature vectorLib =
sig

  include Abbrev

  val VECTOR_ARITH     : term -> thm
  val VECTOR_ARITH_TAC : tactic

end
