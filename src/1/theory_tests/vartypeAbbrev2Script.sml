open HolKernel Parse boolLib

open vartypeAbbrev1Theory

val _ = new_theory "vartypeAbbrev2";

val _ = save_thm("T", TRUTH)


val _ = export_theory();
