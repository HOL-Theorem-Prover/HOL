open HolKernel Parse boolLib bossLib;
open decompileLib backgroundLib;

val _ = new_theory "decompile_test";

(*

(* RISC-V kernel *)

val base_name = "seL4-kernel/riscv/kernel-riscv"
val fast = false;
val res = decomp base_name fast "trap_entry";

val _ = not (!has_failures) orelse failwith "There were failures.";

(* ARM kernel *)

val base_name = "seL4-kernel/arm/kernel"
val fast = false;
val ignore_names = "fastpath_restore,restore_user_context,_start,arm_prefetch_abort_exception,arm_data_abort_exception";
val res = decomp base_name fast ignore_names;

val _ = not (!has_failures) orelse failwith "There were failures.";

*)

(* RISC-V example *)

val base_name = "seL4-kernel/riscv/kernel-riscv"
val fast = false;
val res = decomp_only base_name fast
  ["memzero", "memcpy", "write_slot", "emptySlot", "lookupSlot",
   "resolveAddressBits"];

val _ = not (!has_failures) orelse failwith "There were failures.";

(* ARMv7 example *)

val base_name = "loop/example";
val fast = false;
val ignore_names = "";
val res = decomp base_name fast ignore_names;

val _ = not (!has_failures) orelse failwith "There were failures.";

(* ARM-M0 *)

val base_name = "loop-m0/example";
val fast = false;
val ignore_names = "";
val res = decomp base_name fast ignore_names;

val _ = export_theory();
