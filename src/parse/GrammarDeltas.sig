signature GrammarDeltas =
sig

  val thy_deltas : {thyname : string} -> term_grammar.user_delta list
  val record_delta : term_grammar.user_delta -> unit

end
