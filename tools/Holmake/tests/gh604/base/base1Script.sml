open HolKernel Parse boolLib

val _ = new_theory "base1";

val base1_theorem = save_thm("base1_theorem",
  SPEC “p:bool” AND_CLAUSES);

val _ = export_theory();
