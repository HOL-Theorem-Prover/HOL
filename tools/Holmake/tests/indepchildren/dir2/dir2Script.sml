open HolKernel Parse boolLib

open intermediateLib

val _ = new_theory "dir2";

val dir2_def = new_definition ("dir2_def", “dir2 x <=> base x /\ T”);


val _ = export_theory();
