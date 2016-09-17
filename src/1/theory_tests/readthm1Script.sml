open HolKernel Parse boolLib

val _ = new_theory "readthm1";

val read = save_thm("read", TRUTH);


val _ = export_theory();
