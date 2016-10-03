signature GrammarDeltas =
sig

  val thy_deltas : {thyname : string} ->
                   type_grammar.delta list * term_grammar.user_delta list
  val record_tmdelta : term_grammar.user_delta -> unit
  val record_tydelta : type_grammar.delta -> unit

end
