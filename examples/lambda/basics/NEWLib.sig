signature NEWLib =
sig

  include Abbrev
  val NEW_TAC : string -> term -> tactic
  val NEW_ELIM_TAC : tactic

end;
