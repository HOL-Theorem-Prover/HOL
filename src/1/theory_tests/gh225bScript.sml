open HolKernel Parse boolLib

open gh225aTheory

val _ = new_theory "gh225b";

val _ = save_thm("TRUTH", TRUTH);

val _ = export_theory();
