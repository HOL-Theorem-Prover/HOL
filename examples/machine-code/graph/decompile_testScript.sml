open HolKernel Parse boolLib bossLib;
open decompileLib;

val _ = new_theory "decompile_test";

(* RISC-V *)

(* val base_name = "loop-riscv/example" *)
val base_name = "kernel-riscv/kernel-riscv"
val fast = false;
val ignore_names = "";
val res = decomp base_name fast ignore_names;

(*
(* ARMv7 *)

val base_name = "loop/example";
val fast = false;
val ignore_names = "";
val res = decomp base_name fast ignore_names;

(* ARM-M0 *)

val base_name = "loop-m0/example";
val fast = false;
val ignore_names = "";
val res = decomp base_name fast ignore_names;
*)

val _ = export_theory();
