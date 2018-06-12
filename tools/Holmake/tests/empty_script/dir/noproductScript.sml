open HolKernel Parse boolLib

val _ = new_theory "noproduct";


val foo_def = save_thm("foo_def", TRUTH);
