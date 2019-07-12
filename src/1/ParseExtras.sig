signature ParseExtras =
sig

  val tight_equality : unit -> unit
  val loose_equality : unit -> unit
  val temp_tight_equality : unit -> unit
  val temp_loose_equality : unit -> unit
  val grammar_loose_equality : term_grammar.grammar -> term_grammar.grammar
  val grammar_tight_equality : term_grammar.grammar -> term_grammar.grammar

  val condprinter : term_grammar.userprinter

end
