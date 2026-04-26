open HolKernel boolLib sharedTheory

val _ = new_theory "dirB";

val dirB_thm = save_thm("dirB_thm", shared_thm);

val _ = export_theory();
