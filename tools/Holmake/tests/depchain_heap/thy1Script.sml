open HolKernel Parse boolLib

val _ = new_theory "thy1";

val f_def = new_definition(
  "f_def",
  ``f g x = g (g x)``);

val _ = export_theory();
