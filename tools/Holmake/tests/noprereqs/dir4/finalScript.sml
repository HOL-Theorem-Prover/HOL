open HolKernel Parse boolLib

open derivedTheory

val _ = new_theory "final";

val baz_def = new_definition("baz_def", “baz x <=> (foo x ==> bar x)”);


val _ = export_theory();
