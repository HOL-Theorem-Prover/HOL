open HolKernel Parse boolLib bossLib moduleATheory;
val _ = new_theory "moduleB";
val from_a = save_thm ("from_a", module_value_def);
Definition b_value_def:
  b_value = module_value
End
Theorem b_value_thm[simp]:
  b_value = ModuleValue
Proof
  rw [b_value_def, module_value_def]
QED
val _ = export_theory ();
