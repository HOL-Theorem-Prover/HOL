Theory addMLdep1[bare]
Libs
  HolKernel Parse boolLib

val _ = add_ML_dependency "MLdepLib"

val thm = save_thm("thm", TRUTH);


