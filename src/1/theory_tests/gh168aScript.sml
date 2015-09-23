open HolKernel Parse boolLib

open gh294aTheory gh294bTheory

val _ = new_theory "gh168a";

val thy =
    Binarymap.find(type_grammar.privileged_abbrevs (type_grammar()), "foo")

val _ = disable_tyabbrev_printing (thy^"$foo")

val s = type_to_string ``:bool -> bool -> bool``

val _ = if thy = "gh294a" then assert (equal ":gh294b$foo") s
        else assert (equal ":bool -> gh294a$foo") s

val _ = export_theory();
