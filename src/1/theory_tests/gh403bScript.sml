open HolKernel boolLib gh403aTheory

val _ = new_theory "gh403b";

val _ = save_thm("foo", TRUTH)

val _ = export_theory();
