open HolKernel Parse boolLib

open thy2Theory

val _ = new_theory "thy3";

val _ = save_thm("TRUTH", TRUTH)

val _ = export_theory();
