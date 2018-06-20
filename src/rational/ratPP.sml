structure ratPP =
struct

val _ = term_grammar.userSyntaxFns.register_userPP
          {name = "rat.decimalfractions",
           code = DecimalFractionPP.fraction{Thy = "rat",
                                             Division = "rat_div",
                                             fromNum = "rat_of_num"}}

end
