
open HolKernel boolLib bossLib Parse;
open wordsTheory;

val _ = new_theory "ppc_coretypes";


(* ---------------------------------------------------------------------------------- *>

  This theory defines the types and operations over these types for the PowerPC model.

<* ---------------------------------------------------------------------------------- *)

(* used by the AST *)

val _ = type_abbrev("ireg",``:word5``);
val _ = type_abbrev("freg",``:word5``);
val _ = type_abbrev("ppc_constant",``:word16``);
val _ = type_abbrev("crbit",``:word2``);

(* used elsewhere *)

val _ = Hol_datatype `
  ppc_bit = PPC_CARRY     (* carry bit of the status register *)
          | PPC_CR0 of word2  (* bit i of the condition register  *)`;

val _ = Hol_datatype `
  ppc_reg = PPC_IR of word5  (* integer registers *) 
          | PPC_LR           (* link register (return address) *)
          | PPC_CTR          (* count register, used for some branches *)
          | PPC_PC           (* program counter *)`;

val _ = Hol_datatype   `iiid = <| proc : num ; program_order_index : num |>`;


val _ = export_theory ();
