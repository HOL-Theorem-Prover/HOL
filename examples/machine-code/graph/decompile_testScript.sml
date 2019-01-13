open HolKernel Parse boolLib bossLib;
open decompileLib;

val _ = new_theory "decompile_test";

(* ARMv7 code *)

val base_name = "loop/example";
val fast = false;
val ignore_names = "";
val res = decomp base_name fast ignore_names;

val _ = export_theory();
