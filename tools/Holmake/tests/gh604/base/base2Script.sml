open HolKernel Parse boolLib

val _ = new_theory "base2";

val base1_theorem = save_thm("base2_theorem",
  SPEC “q:bool” AND_CLAUSES);

val _ = export_theory();
