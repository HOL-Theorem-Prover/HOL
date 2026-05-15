signature head_reductionLib =
sig
  include Abbrev

  val HNF_TAC    : term * term * term * term -> term -> tactic
  val T_TAC      : tactic
  val UNBETA_TAC : thm list -> term -> tactic
  val unbeta_tac : thm list -> term -> tactic

end
