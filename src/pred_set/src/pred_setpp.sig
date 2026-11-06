signature pred_setpp =
sig

  val univ_printer : term_grammar.userprinter

  val setcomprehension_printer : term_grammar.userprinter

  val univ_printing              : HOLFlags.bflag
  val unicode_univ               : HOLFlags.bflag
  val unambiguous_comprehensions : HOLFlags.flag

end
