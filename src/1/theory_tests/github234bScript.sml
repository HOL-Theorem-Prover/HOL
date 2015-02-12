open HolKernel Parse boolLib

open github234aTheory

val _ = new_theory "github234b";

val _ = save_thm("T", TRUTH)


val _ = export_theory();
