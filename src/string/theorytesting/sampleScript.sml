
open HolKernel Parse boolLib bossLib stringTheory;
val _ = new_theory "sample";

val _ = Define `badstring = "*)"`;

(* val _ = max_print_depth := 0; *)
val _ = export_theory();

