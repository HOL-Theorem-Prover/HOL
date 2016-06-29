signature monadsyntax =
sig

  (* loading this module installs this function as an absyn transformer
     under the name "monadsyntax.transform_absyn"
  *)
  val transform_absyn : term_grammar.absyn_postprocessor

end
