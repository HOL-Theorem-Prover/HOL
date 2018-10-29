open HolKernel Parse boolLib

val _ = new_theory "final";

val final_theorem = save_thm("final_theorem",
  CONJ base2Theory.base2_theorem midTheory.mid_theorem);

val _ = export_theory();
