open HolKernel Parse boolLib

val _ = new_theory "gh294b";

val _ = type_abbrev("foo", ``:bool -> bool -> bool``)


val _ = export_theory();
