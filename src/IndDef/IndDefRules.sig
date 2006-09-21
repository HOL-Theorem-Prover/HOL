signature IndDefRules =
sig
  include Abbrev

  val REDUCE   : conv
  val RULE_TAC : thm -> tactic
  val RULE_INDUCT_THEN : thm -> (thm -> tactic) -> (thm -> tactic) -> tactic

  val derive_mono_strong_induction : InductiveDefinition.monoset -> thm * thm -> thm

end
