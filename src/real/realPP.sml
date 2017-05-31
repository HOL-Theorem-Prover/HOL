structure realPP =
struct

val _ = term_grammar.userSyntaxFns.register_userPP
          {name = "real.decimalfractions",
           code = DecimalFractionPP.fraction{Thy = "real",
                                             Division = "/",
                                             fromNum = "real_of_num"}}

end
