open HolKernel Parse boolLib

val _ = new_theory "gh225a";

val _ = save_thm("Empty", TRUTH);
val _ = save_thm("GREATER", TRUTH);


val _ = export_theory();
