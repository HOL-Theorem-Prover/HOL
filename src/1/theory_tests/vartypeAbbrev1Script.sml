Theory vartypeAbbrev1[bare]
Libs
  HolKernel Parse boolLib

val _ = type_abbrev("foo", ``:'aa -> bool``)
val _ = save_thm("T", TRUTH)


