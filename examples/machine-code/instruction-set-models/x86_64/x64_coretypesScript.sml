
open HolKernel boolLib bossLib Parse;
open wordsTheory listTheory;

val _ = new_theory "x64_coretypes";


(* ---------------------------------------------------------------------------------- *>

  This theory defines the types and operations over these types for the x64 model.

<* ---------------------------------------------------------------------------------- *)

(* used by the AST *)

val _ = Hol_datatype `Zreg = RAX | RBX | RCX  | RDX  | RSP  | RBP  | RSI  | RDI  |
                             zR8 | zR9 | zR10 | zR11 | zR12 | zR13 | zR14 | zR15 `;

val _ = Hol_datatype `Zsize = Z8 | Z16 | Z32 | Z64`;

(* used elsewhere *)

val _ = Hol_datatype `
  Zeflags = Z_CF | Z_PF | Z_AF | Z_ZF | Z_SF | Z_OF `;

val _ = Hol_datatype `
  Zea =
      Zea_i of Zsize => word64   (* constant       *)
    | Zea_r of Zsize => Zreg     (* register name  *)
    | Zea_m of Zsize => word64   (* memory address *) `;

val _ = Hol_datatype   `iiid = <| proc : num ; program_order_index : num |>`;


(* distinctness theorem *)

val ALL_DISTINCT_Zreg = store_thm("ALL_DISTINCT_Zreg",
  ``ALL_DISTINCT ([RAX;RCX;RDX;RBX;RSP;RBP;RSI;RDI;zR8;zR9;zR10;zR11;zR12;zR13;zR14;zR15]:Zreg list)``,
  SIMP_TAC std_ss (ALL_DISTINCT::MEM::fetch "-" "num2Zreg_11"::map (fetch "-")
       ["RAX","RCX","RDX","RBX","RSP","RBP","RSI","RDI","zR8","zR9","zR10","zR11","zR12","zR13","zR14","zR15"]));


val _ = export_theory ();
