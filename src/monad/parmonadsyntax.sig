signature parmonadsyntax =
sig

  val monad_bind : string
  val monad_par : string
  val ass_prec : int
  val par_prec : int

  val print_monads : term_grammar.userprinter

  (* loading this module installs this function as an absyn transformer
     under the name "parmonadsyntax.transform_absyn"
  *)
  val transform_absyn : term_grammar.absyn_postprocessor

end
