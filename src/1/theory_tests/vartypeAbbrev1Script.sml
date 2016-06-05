open HolKernel Parse boolLib

val _ = new_theory "vartypeAbbrev1";

val _ = type_abbrev("foo", ``:'aa -> bool``)
val _ = save_thm("T", TRUTH)


val _ = export_theory();
