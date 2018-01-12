open HolKernel Parse boolLib

open intermediateLib

val _ = new_theory "dir1";

val dir1_def = new_definition("dir1_def", “dir1 x = base x \/ F”);


val _ = export_theory();
