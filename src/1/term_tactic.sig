signature term_tactic =
sig

  type tactic = Tactic.tactic
  type term = Term.term
  type term_tactic = term -> tactic
  val goal_term : term_tactic -> tactic
  val subtm_assum_term : term -> term_tactic -> tactic
  val first_assum_term : term_tactic -> tactic
  val last_assum_term : term_tactic -> tactic
  val first_fv_term : term_tactic -> tactic
  val fv_term : term_tactic -> tactic

end
