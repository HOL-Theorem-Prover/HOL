signature parmonadsyntax =
sig

  val monad_bind : string
  val monad_par : string
  val ass_prec : int
  val par_prec : int

  val print_monads : term_grammar.userprinter

end
