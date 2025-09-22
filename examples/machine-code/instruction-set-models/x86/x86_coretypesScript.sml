
Theory x86_coretypes
Ancestors
  words bit_list list

(* ---------------------------------------------------------------------------------- *>

  This theory defines the types and operations over these types for the x86 model.

<* ---------------------------------------------------------------------------------- *)

(* used by the AST *)

(* type of address values and of values stored in registers *)
val _ = type_abbrev("Ximm",``:word32``);

val _ = Hol_datatype `Xreg = EAX | EBX | ECX | EDX | ESP | EBP | ESI | EDI `;

(* used elsewhere *)

val _ = Hol_datatype `
  Xeflags = X_CF | X_PF | X_AF | X_ZF | X_SF | X_OF `;

val _ = Hol_datatype `
  Xea =
      Xea_i of Ximm     (* constant       *)
    | Xea_r of Xreg     (* register name  *)
    | Xea_m of word32   (* memory address *) `;

val _ = Hol_datatype   `iiid = <| proc : num ;
             program_order_index : num |>`;



