open HolKernel Parse boolLib

open readthm1Theory

val _ = new_theory "readthm2";

val next_thm = save_thm("next_thm", CONJ read read)


val _ = export_theory();
