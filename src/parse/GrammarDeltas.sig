signature GrammarDeltas =
sig

  type 'a enc = 'a ThyDataSexp.enc
  type 'a dec = 'a ThyDataSexp.dec
  type tmg_delta = term_grammar.user_delta
  type tyg_delta = type_grammar.delta
  datatype gdelta = TYD of tyg_delta | TMD of tmg_delta
  val grammar_rule_decode : term_grammar_dtype.grammar_rule dec
  val grammar_rule_encode : term_grammar_dtype.grammar_rule enc

  val user_delta_decode : tmg_delta dec
  val user_delta_encode : tmg_delta enc
  val fixity_encode : term_grammar_dtype.fixity enc
  val fixity_decode : term_grammar_dtype.fixity dec
  val grule_encode : term_grammar_dtype.grule enc
  val grule_decode : term_grammar_dtype.grule dec

  val tydelta_encode : tyg_delta enc
  val tydelta_decode : tyg_delta dec
  val gdelta_encode : gdelta enc
  val gdelta_decode : gdelta dec

  val thy_deltas : {thyname : string} -> gdelta list
  val record_tmdelta : term_grammar.user_delta -> unit
  val record_tydelta : type_grammar.delta -> unit
  val clear_deltas : unit -> unit

end
