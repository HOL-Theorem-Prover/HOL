signature DecimalFractionPP =
sig

  val fraction : {Thy:string,Division:string,fromNum:string} ->
                 term_grammar.userprinter

end
