open HolKernel Parse boolLib

open loadDatatypeATheory

val _ = new_theory "loadDatatypeB";

val _ = save_thm("T", TRUTH)

val _ = export_theory();
