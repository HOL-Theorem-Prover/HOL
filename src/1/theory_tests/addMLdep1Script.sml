open HolKernel Parse boolLib

val _ = new_theory "addMLdep1";

val _ = add_ML_dependency "MLdepLib"

val thm = save_thm("thm", TRUTH);


val _ = export_theory();
