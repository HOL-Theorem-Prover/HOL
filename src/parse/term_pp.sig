local
  type term_grammar = term_grammar.grammar
  type type_grammar = parse_type.grammar
  open HolKernel
in

val pp_term :
  term_grammar -> type_grammar -> Portable.ppstream -> term -> unit

end