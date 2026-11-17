signature wordspp =
sig

  val words_printer : term_grammar.userprinter
  val words_cast_printer : term_grammar.userprinter

  val printing       : HOLFlags.flag
  val cast_printing  : HOLFlags.bflag
  val pp_as_2s_comp  : HOLFlags.bflag

end
