signature parse_term =
sig
  type 'a PStack
  type 'a qbuf = 'a qbuf.qbuf
  type term = Term.term
  datatype stack_terminal = datatype parse_term_dtype.stack_terminal
  val STtoString : term_grammar.grammar -> stack_terminal -> string

  val initial_pstack : 'a PStack
  val is_final_pstack : 'a PStack -> bool
  val top_nonterminal : term PStack -> Absyn.absyn

  exception PrecConflict of stack_terminal * stack_terminal
  exception ParseTermError of string locn.located

  val parse_term :
      term_grammar.grammar ->
      (term qbuf -> Pretype.pretype) ->
      (term qbuf * term PStack, unit, string locn.located) errormonad.t

  datatype mx_order = datatype parse_term_dtype.mx_order
  val mk_prec_matrix :
      term_grammar.grammar ->
      ((stack_terminal * bool) * stack_terminal, mx_order) Binarymap.dict Unsynchronized.ref

end
