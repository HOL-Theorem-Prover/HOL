signature parse_term = sig
  local
    open term_grammar monadic_parse
  in
    datatype 'a varstruct =
      SIMPLE of string | VPAIR of ('a varstruct * 'a varstruct) |
      TYPEDV of 'a varstruct * 'a parse_type.pretype |
      RESTYPEDV of 'a varstruct * 'a preterm | VS_AQ of 'a
    and 'a preterm =
      COMB of ('a preterm * 'a preterm) | VAR of string |
      ABS of ('a varstruct * 'a preterm) | AQ of 'a |
      TYPED of ('a preterm * 'a parse_type.pretype)

    val strip_comb : 'a preterm -> ('a preterm * 'a preterm list)

    datatype 'a lookahead_item =
      Token of 'a term_tokens.term_token |
      PreType of 'a parse_type.pretype

    datatype 'a stack_item =
      Terminal of stack_terminal |
      NonTerminal of 'a preterm |
      NonTermVS of 'a varstruct list

    datatype 'a PStack =
      PStack of {stack : ('a stack_item * 'a lookahead_item) list,
                 lookahead : 'a lookahead_item list,
                 in_vstruct : bool}
    val pstack : 'a PStack -> ('a stack_item * 'a lookahead_item) list

    exception PrecConflict of stack_terminal * stack_terminal

    val parse_term :
      grammar -> (''a parse_type.pretype, ''a frag) Parser ->
      (''a frag list * ''a PStack) ->
      (''a frag list * ''a PStack) * unit option

    val remove_specials : 'a preterm -> 'a preterm

  end
end

