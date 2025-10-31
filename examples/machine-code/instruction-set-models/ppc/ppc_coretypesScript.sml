
Theory ppc_coretypes
Ancestors
  words

(* ---------------------------------------------------------------------------------- *>

  This theory defines the types and operations over these types for the PowerPC model.

<* ---------------------------------------------------------------------------------- *)

(* used by the AST *)

val _ = type_abbrev("ireg",``:word5``);
val _ = type_abbrev("freg",``:word5``);
val _ = type_abbrev("ppc_constant",``:word16``);
val _ = type_abbrev("crbit",``:word2``);

(* used elsewhere *)

Datatype:
  ppc_bit = PPC_CARRY      (* carry bit of the status register *)
          | PPC_CR0 word2  (* bit i of the condition register  *)
End

Datatype:
  ppc_reg = PPC_IR word5     (* integer registers *)
          | PPC_LR           (* link register (return address) *)
          | PPC_CTR          (* count register, used for some branches *)
          | PPC_PC           (* program counter *)
End

Datatype: iiid = <| proc : num ; program_order_index : num |>
End
