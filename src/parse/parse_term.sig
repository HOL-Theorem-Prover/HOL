signature parse_term = sig
  local
    open term_grammar monadic_parse
  in
    type 'a PStack
    val initial_pstack : 'a PStack
    val is_final_pstack : 'a PStack -> bool
    val top_nonterminal : Term.term PStack -> Absyn.absyn

    exception PrecConflict of stack_terminal * stack_terminal
    exception ParseTermError of string

    val parse_term :
      grammar -> (TCPretype.pretype, ''a frag) Parser ->
      (unit -> string list) -> (* ancestry function *)
      (''a frag list * ''a PStack) ->
      (''a frag list * ''a PStack) * unit option

  end
end

