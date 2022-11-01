signature relation_extraLib =
sig

  include Abbrev

  val gen_rewrite   : (int * int) -> thm_tactic
  val left_rewrite  : thm_tactic
  val rewrite       : thm_tactic
  val right_rewrite : thm_tactic

  val rsubset_tac   : tactic

  val rel_ss        : unit -> simpLib.simpset
  val xfs           : thm list -> tactic
  val xrw           : thm list -> tactic
  val xsimp         : thm list -> tactic

end
