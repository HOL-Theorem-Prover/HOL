signature IndDefRules =
sig
  include Abbrev

  val REDUCE   : conv
  val RULE_TAC : thm -> tactic
  val RULE_INDUCT_THEN : thm -> (thm -> tactic) -> (thm -> tactic) -> tactic
  val derive_strong_induction : thm list * thm -> thm

end
