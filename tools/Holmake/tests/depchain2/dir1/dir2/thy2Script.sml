open HolKernel Parse boolLib

open thy1Theory

val _ = new_theory "thy2";

val g_def = new_definition("g_def",
  ``g x y = y /\ f x``);


val _ = export_theory();
