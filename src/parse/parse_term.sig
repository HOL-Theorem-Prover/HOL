signature parse_term = sig
    type 'a PStack
    val initial_pstack : 'a PStack
    val is_final_pstack : 'a PStack -> bool
    val top_nonterminal : Term.term PStack -> Absyn.absyn

    exception PrecConflict of
      term_grammar.stack_terminal * term_grammar.stack_terminal
    exception ParseTermError of string

    val parse_term :
      term_grammar.grammar ->
      (Pretype.pretype, ''a frag) monadic_parse.Parser ->
      (''a frag list * ''a PStack) ->
      (''a frag list * ''a PStack) * unit option

end

