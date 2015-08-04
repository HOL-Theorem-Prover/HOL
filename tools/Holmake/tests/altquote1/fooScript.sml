open HolKernel Parse boolLib

val _ = new_theory "foo";

val foo_def = new_definition("foo_def", “foo P x <=> P x”);

val _ = export_theory();
