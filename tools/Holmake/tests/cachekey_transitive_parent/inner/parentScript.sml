open HolKernel Parse boolLib

val _ = new_theory "parent";
val parent_thm = save_thm("parent_thm", TRUTH);
val _ = export_theory();
