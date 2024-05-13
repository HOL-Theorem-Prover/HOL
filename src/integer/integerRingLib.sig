signature integerRingLib =
sig
  include Abbrev

  val INT_NORM_CONV : conv
  val INT_RING_CONV : conv

  val INT_NORM_TAC : tactic
  val INT_RING_TAC : tactic

  val INT_NORM_RULE : thm -> thm
  val INT_RING_RULE : thm -> thm

  val INT_POLY_CONV       : conv
  val INT_RING            : term -> thm
  val int_ideal_cofactors : term list -> term -> term list

end
