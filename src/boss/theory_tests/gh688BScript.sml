open HolKernel Parse boolLib bossLib;

open gh688ATheory
val _ = new_theory "gh688B";

val _ = set_trace "Unicode" 0
val _ = List.app testutils.tpp ["foo 3", "{x | x <= 10}"]

val _ = export_theory();
