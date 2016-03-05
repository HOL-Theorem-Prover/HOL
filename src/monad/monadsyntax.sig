signature monadsyntax =
sig

  (* loading this module installs this function as an absyn transformer
     under the name "monadsyntax.transform_absyn"
  *)
  val transform_absyn : Absyn.absyn -> Absyn.absyn

end
