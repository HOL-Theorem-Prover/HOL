Theory gh168a[bare]
Ancestors
  gh294a gh294b
Libs
  HolKernel Parse boolLib

val thy =
    Binarymap.find(type_grammar.privileged_abbrevs (type_grammar()), "foo")

val _ = disable_tyabbrev_printing (thy^"$foo")

val s = type_to_string ``:bool -> bool -> bool``

val _ = if thy = "gh294a" then assert (equal ":gh294b$foo") s
        else assert (equal ":bool -> gh294a$foo") s

