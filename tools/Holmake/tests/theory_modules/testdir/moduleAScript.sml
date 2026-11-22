open HolKernel Parse boolLib bossLib;
val _ = new_theory "moduleA";
Datatype `module_type = ModuleValue`;
Definition module_value_def:
  module_value = ModuleValue
End
(* MODULE_A_CONSTANT=1 adds a constant named like the type: theories that
   refer to the type keep their .dat files, yet their modules no longer
   fit the kernel. *)
val _ = if OS.Process.getEnv "MODULE_A_CONSTANT" = SOME "1"
        then new_constant ("module_type", bool) else ();
val _ = export_theory ();
