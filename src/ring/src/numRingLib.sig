signature numRingLib =
sig
  include Abbrev 

  val NUM_NORM_CONV : conv
  val NUM_RING_CONV : conv

  val NUM_NORM_TAC : tactic
  val NUM_RING_TAC : tactic

  val NUM_NORM_RULE : thm -> thm
  val NUM_RING_RULE : thm -> thm

end
