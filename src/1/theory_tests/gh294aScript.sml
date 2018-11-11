open HolKernel Parse boolLib

val _ = new_theory "gh294a";

val _ = type_abbrev_pp("foo", ``:bool -> bool``)


val _ = export_theory();
