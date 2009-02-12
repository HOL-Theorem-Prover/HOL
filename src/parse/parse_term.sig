signature parse_term =
sig
  type 'a PStack
  type 'a qbuf= 'a qbuf.qbuf
  type stack_terminal = term_grammar.stack_terminal
  val initial_pstack : 'a PStack
  val is_final_pstack : 'a PStack -> bool
  val top_nonterminal : Term.term PStack -> Absyn.absyn

  exception PrecConflict of stack_terminal * stack_terminal
  exception ParseTermError of string locn.located

  val parse_term :
      term_grammar.grammar ->
      (''a qbuf -> Pretype.pretype) ->
      (''a qbuf * ''a PStack) ->
      (''a qbuf * ''a PStack) * unit option

  (* not used externally, but can be useful for debugging *)
  datatype mx_src = Ifx | Pfx | MS_Other | MS_Multi
  datatype mx_order = PM_LESS of mx_src
                    | PM_GREATER of mx_src
                    | PM_EQUAL
                    | PM_LG of {pfx:order,ifx:order}

  val mk_prec_matrix :
      term_grammar.grammar ->
      ((stack_terminal * bool) * stack_terminal, mx_order) Binarymap.dict ref


end

