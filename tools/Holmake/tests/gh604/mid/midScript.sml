open HolKernel Parse boolLib

val _ = new_theory "mid";

val base1_theorem = save_thm("mid_theorem",
  CONJUNCT1 base1Theory.base1_theorem);

val _ = export_theory();
