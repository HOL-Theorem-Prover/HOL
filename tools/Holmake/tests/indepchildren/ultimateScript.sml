open HolKernel Parse boolLib ;

open dir2Theory

val _ = new_theory "ultimate";

val ultimate = save_thm("ultimate", TRUTH)


val _ = export_theory();
