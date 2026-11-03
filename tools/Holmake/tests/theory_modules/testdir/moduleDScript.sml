open HolKernel Parse boolLib bossLib moduleBTheory moduleCTheory;
val _ = new_theory "moduleD";
val from_b = save_thm ("from_b", moduleBTheory.from_a);
val from_c = save_thm ("from_c", moduleCTheory.from_a);
val _ = export_theory ();
