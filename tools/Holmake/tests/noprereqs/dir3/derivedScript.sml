open HolKernel Parse boolLib

open baseLib

val _ = new_theory "derived";

val bar_def = new_definition("bar_def", “bar x <=> x \/ T”);

val _ = export_theory();
