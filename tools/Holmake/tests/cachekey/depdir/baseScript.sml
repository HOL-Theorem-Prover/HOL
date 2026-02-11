open HolKernel Parse boolLib

val _ = new_theory "base";

val base_thm = save_thm("base_thm", TRUTH);

val _ = export_theory();
