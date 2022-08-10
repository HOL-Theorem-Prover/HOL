open HolKernel Parse boolLib

open baseTheory

val _ = new_theory "child";

val child = save_thm("child", CONJ base (SPEC_ALL base))


val _ = export_theory();
