open HolKernel Parse boolLib

val _ = new_theory "base";

val _ = save_thm("baseTRUTH", TRUTH)

val _ = export_theory();
