open HolKernel Parse boolLib bossLib;
val _ = new_theory "moduleA";
Datatype `module_type = ModuleValue`;
Definition module_value_def:
  module_value = ModuleValue
End
val _ = export_theory ();
