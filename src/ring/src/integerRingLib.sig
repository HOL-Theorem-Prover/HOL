signature integerRingLib =
sig
  include Abbrev 

  val INT_NORM_CONV : conv
  val INT_RING_CONV : conv

  val INT_NORM_TAC : tactic
  val INT_RING_TAC : tactic

  val INT_NORM_RULE : thm -> thm
  val INT_RING_RULE : thm -> thm

end
