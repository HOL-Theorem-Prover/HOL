open HolKernel boolLib

val _ = new_theory "gh403a"

val _ = save_thm("print",TRUTH);

val _ = export_theory();
