signature term_pp =
sig

  val pp_term :
    term_grammar.grammar -> type_grammar.grammar -> Portable.ppstream ->
    Term.term -> unit

end;


