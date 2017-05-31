signature monadsyntax =
sig

  (* loading this module installs this function as an absyn transformer
     under the name "monadsyntax.transform_absyn"
  *)
  val transform_absyn : term_grammar.absyn_postprocessor
  val print_monads : term_grammar.userprinter

  val add_monadsyntax : unit -> unit
  val temp_add_monadsyntax : unit -> unit

end
