signature boolpp =
sig

  val condprinter : term_grammar.userprinter
  val letprinter : term_grammar.userprinter
  val let_processor : term_grammar.absyn_postprocessor

end
