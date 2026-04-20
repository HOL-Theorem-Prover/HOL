open HolKernel boolLib sharedTheory

val _ = new_theory "dirA";

val dirA_thm = save_thm("dirA_thm", shared_thm);

val _ = export_theory();
