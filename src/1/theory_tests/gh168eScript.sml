open HolKernel Parse boolLib

open gh294aTheory gh294bTheory testutils

val _ = new_theory "gh168e";

val b2b = bool --> bool
val b2b2b = bool --> b2b

val tyg0 = type_grammar()
val privthy = Binarymap.find(type_grammar.privileged_abbrevs tyg0, "foo")
val unprivthy = if privthy = "gh294a" then "gh294b" else "gh294a"

val (privty, unprivty) = if privthy = "gh294a" then (b2b, b2b2b)
                         else (b2b2b, b2b)

val ty = ``:foo``
val _ = assert (equal privty) ty

val _ = temp_thytype_abbrev ({Name = "foo", Thy = unprivthy}, unprivty)

val ty = ``:foo``
val _ = assert (equal unprivty) ty

val _ = export_theory();
