
Theory x86_coretypes
Ancestors
  words bit_list list

(* ---------------------------------------------------------------------------------- *>

  This theory defines the types and operations over these types for the x86 model.

<* ---------------------------------------------------------------------------------- *)

(* used by the AST *)

(* type of address values and of values stored in registers *)
val _ = type_abbrev("Ximm",``:word32``);

Datatype: Xreg = EAX | EBX | ECX | EDX | ESP | EBP | ESI | EDI
End

(* used elsewhere *)

Datatype:
  Xeflags = X_CF | X_PF | X_AF | X_ZF | X_SF | X_OF
End

Datatype:
  Xea =
      Xea_i of Ximm     (* constant       *)
    | Xea_r of Xreg     (* register name  *)
    | Xea_m of word32   (* memory address *)
End

Datatype: iiid = <| proc : num ;
             program_order_index : num |>
End



