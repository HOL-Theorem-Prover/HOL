open HolKernel boolLib

val _ = new_theory "shared";

val shared_thm = save_thm("shared_thm", TRUTH);

val _ = export_theory();
