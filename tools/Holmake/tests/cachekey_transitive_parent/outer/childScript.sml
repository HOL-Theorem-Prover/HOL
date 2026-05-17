open HolKernel Parse boolLib
open parentLib

val _ = new_theory "child";
val child_thm = save_thm("child_thm", parent_thm);
val _ = export_theory();
