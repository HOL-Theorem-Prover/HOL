open HolKernel Parse boolLib bossLib;

val _ = new_theory "thy2";

val g_def = new_definition(
  "g_def",
  ``g x = x * 2``);


val _ = export_theory();
