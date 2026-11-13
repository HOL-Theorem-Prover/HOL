open HolKernel Parse boolLib bossLib moduleATheory;
val _ = new_theory "moduleC";
val from_a = save_thm ("from_a", module_value_def);
val _ = export_theory ();
