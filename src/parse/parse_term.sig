signature parse_term = sig
  local
    open term_grammar monadic_parse
  in
    datatype 'a varstruct =
      SIMPLE of string | VPAIR of ('a varstruct * 'a varstruct) |
      TYPEDV of 'a varstruct * TCPretype.pretype |
      RESTYPEDV of 'a varstruct * 'a preterm | VS_AQ of 'a
    and 'a preterm =
      COMB of ('a preterm * 'a preterm) | VAR of string |
      ABS of ('a varstruct * 'a preterm) | AQ of 'a |
      TYPED of ('a preterm * TCPretype.pretype)

    val strip_comb : 'a preterm -> ('a preterm * 'a preterm list)

    datatype 'a lookahead_item =
      Token of 'a term_tokens.term_token |
      PreType of TCPretype.pretype |
      LA_Symbol of stack_terminal

    datatype 'a stack_item =
      Terminal of stack_terminal |
      NonTerminal of 'a preterm |
      NonTermVS of 'a varstruct list

    datatype vsres_state = VSRES_Normal | VSRES_VS | VSRES_RESTM
    datatype 'a PStack =
      PStack of {stack : ('a stack_item * 'a lookahead_item) list,
                 lookahead : 'a lookahead_item list,
                 in_vstruct : (vsres_state * int) list}
    val pstack : 'a PStack -> ('a stack_item * 'a lookahead_item) list

    exception PrecConflict of stack_terminal * stack_terminal
    exception ParseTermError of string

    val parse_term :
      grammar -> (TCPretype.pretype, ''a frag) Parser ->
      (unit -> string list) -> (* ancestry function *)
      (''a frag list * ''a PStack) ->
      (''a frag list * ''a PStack) * unit option

    val remove_specials : 'a preterm -> 'a preterm

  end
end

