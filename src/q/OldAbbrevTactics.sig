signature OldAbbrevTactics =
sig
  include Abbrev

  val ABBREV_TAC     : term quotation -> tactic
  val UNABBREV_TAC   : term quotation -> tactic
  val PAT_ABBREV_TAC : term quotation -> tactic

end
