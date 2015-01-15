open HolKernel Parse boolLib

open gh224aTheory

val _ = new_theory "gh224b";

val _ = save_thm("T", TRUTH)


val _ = export_theory();
