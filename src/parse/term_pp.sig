local
  type term_grammar = term_grammar.grammar
  type type_grammar = parse_type.grammar
  open HolKernel
in

val consume_prefix_spaces : bool ref
val parenthesise_pairs : bool ref
val space_in_pairs : bool ref

val pp_term :
  term_grammar -> type_grammar -> Portable_PrettyPrint.ppstream -> term -> unit

end