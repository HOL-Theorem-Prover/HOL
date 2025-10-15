
Theory x64_coretypes
Ancestors
  words list

(* ---------------------------------------------------------------------------------- *>

  This theory defines the types and operations over these types for the x64 model.

<* ---------------------------------------------------------------------------------- *)

(* used by the AST *)

Datatype: Zreg = RAX | RBX | RCX  | RDX  | RSP  | RBP  | RSI  | RDI  |
                             zR8 | zR9 | zR10 | zR11 | zR12 | zR13 | zR14 | zR15 |
                             (* nothing decodes to the ghost regsiters, it's just ghost state *)
                             zGhost_stack_top | zGhost_stack_bottom
End

Datatype: Zsize = Z8 | Z16 | Z32 | Z64
End

(* used elsewhere *)

Datatype:
  Zeflags = Z_CF | Z_PF | Z_AF | Z_ZF | Z_SF | Z_OF
End

Datatype:
  Zea =
      Zea_i of Zsize => word64     (* constant       *)
    | Zea_r of Zsize => Zreg       (* register name  *)
    | Zea_m of Zsize => word64     (* memory address *)
End

Datatype: iiid = <| proc : num ; program_order_index : num |>
End


(* distinctness theorem *)

val ALL_DISTINCT_Zreg = store_thm("ALL_DISTINCT_Zreg",
  ``ALL_DISTINCT ([RAX;RCX;RDX;RBX;RSP;RBP;RSI;RDI;zR8;zR9;zR10;zR11;
      zR12;zR13;zR14;zR15;zGhost_stack_top;zGhost_stack_bottom]:Zreg list)``,
  SRW_TAC[][]);

