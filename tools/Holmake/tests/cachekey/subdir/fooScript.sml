open HolKernel Parse boolLib

val _ = new_theory "foo";

val foo = save_thm("foo", TRUTH);

val _ = export_theory();
