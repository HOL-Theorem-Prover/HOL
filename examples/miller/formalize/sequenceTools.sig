signature sequenceTools =
sig

  val SEQUENCE_CASES_TAC : Term.term -> Abbrev.tactic
  val SEQ_CASES_TAC : Term.term frag list -> Abbrev.tactic

end