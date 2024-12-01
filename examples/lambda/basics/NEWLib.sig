signature NEWLib =
sig

  include Abbrev
  val NEW_TAC : string -> term -> tactic
  val NEW_ELIM_TAC : tactic

  val RNEWS_TAC : term * term * term -> term -> tactic
  val NEWS_TAC  : term * term -> term -> tactic
end;
