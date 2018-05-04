open HolKernel Parse boolLib

val _ = new_theory "base";

val base_def = new_definition ("base_def", “base x = x /\ T”);

val _ = export_theory();
