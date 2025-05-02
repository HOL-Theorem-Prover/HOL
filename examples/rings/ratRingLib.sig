signature ratRingLib =
sig
  include Abbrev

  val RAT_RING_NORM_CONV : conv
  val RAT_RING_CONV : conv

  val RAT_RING_NORM_TAC : tactic
  val RAT_RING_TAC : tactic

  val RAT_RING_NORM_RULE : thm -> thm
  val RAT_RING_RULE : thm -> thm

end
