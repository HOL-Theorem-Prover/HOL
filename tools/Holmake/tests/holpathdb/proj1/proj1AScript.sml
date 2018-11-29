open HolKernel Parse boolLib

val _ = new_theory "proj1A";

val foo_def = new_definition("foo_def", “foo x = x \/ T”);

val Athm = store_thm("Athm", “!y. foo y”, REWRITE_TAC [foo_def])

val _ = export_theory();
