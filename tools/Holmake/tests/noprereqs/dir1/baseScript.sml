open HolKernel Parse boolLib ;

val _ = new_theory "base";

val foo_def = new_definition("foo_def", “foo x = x /\ T”);


val _ = export_theory();
