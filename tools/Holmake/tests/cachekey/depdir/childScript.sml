open HolKernel Parse boolLib baseTheory

val _ = new_theory "child";

val child_thm = save_thm("child_thm", base_thm);

val _ = export_theory();
