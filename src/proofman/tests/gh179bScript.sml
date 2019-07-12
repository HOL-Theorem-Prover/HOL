open HolKernel Parse boolLib

open gh179aTheory

val _ = new_theory "gh179b";

val foo_tydef = new_type_definition("foo", tyexists)


val _ = export_theory();
