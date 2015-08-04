open HolKernel Parse boolLib

open nextTheory

val _ = new_theory "last";

val _ = save_thm("last", TRUTH)


val _ = export_theory();
