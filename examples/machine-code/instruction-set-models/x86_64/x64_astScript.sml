
open HolKernel boolLib bossLib Parse;

open x64_coretypesTheory;

val _ = new_theory "x64_ast";


(* ---------------------------------------------------------------------------------- *>

  This theory defines the abstract syntax tree (AST) for x64 instructions. It uses

     word64 - type of immediate constant
     Zreg - type of register name

  from x64_coretypesTheory.

<* ---------------------------------------------------------------------------------- *)


val _ = Hol_datatype `
  Zrm = Zr of Zreg                                           (* register *)
      | Zm of (word2 # Zreg) option => Zreg option => word64 (* mem[2^{scale} * index + base + displacement] *)`;

(* check whether rm requires a lock, i.e. specifies a memory access *)

val Zrm_is_memory_access_def = Define `
  (Zrm_is_memory_access (Zm i b d) = T) /\
  (Zrm_is_memory_access (Zr r) = F)`;

val _ = Hol_datatype `                 (* Here XX is one of 8, 16, 32, 64. *)
  Zdest_src = Zrm_i of Zrm  => word64  (* mnemonic r/mXX, immXX (sign-extended) *)
            | Zrm_r of Zrm  => Zreg    (* mnemonic r/mXX, rXX *)
            | Zr_rm of Zreg => Zrm     (* mnemonic rXX, r/mXX *)  `;

val _ = Hol_datatype `
  Zimm_rm = Zi_rm of Zrm      (* r/mXX *)
          | Zi    of word64   (* sign-extended immediate *) `;

val _ = Hol_datatype `Zbinop_name = Zadc | Zadd | Zand | Zcmp | Zor | Zshl | Zshr | Zsar | Zsub | Zsbb | Ztest | Zxor `;
val _ = Hol_datatype `Zmonop_name = Zdec | Zinc | Znot | Zneg `;

val _ = Hol_datatype `Zcond = (* this list is not complete *)
    Z_ALWAYS            (* N = not     *)
  | Z_E | Z_NE          (* E = equal   *)
  | Z_S | Z_NS          (* S = signed  *)
  | Z_A | Z_NA          (* A = above   *)
  | Z_B | Z_NB          (* B = below   *)`;

val _ = Hol_datatype `
  Zinstruction = Zbinop     of Zbinop_name => Zsize => Zdest_src
               | Zmonop     of Zmonop_name => Zsize => Zrm
               | Zcmpxchg   of Zsize => Zrm => Zreg
               | Zxadd      of Zsize => Zrm => Zreg
               | Zxchg      of Zsize => Zrm => Zreg
               | Zmul       of Zsize => Zrm
               | Zdiv       of Zsize => Zrm
               | Zlea       of Zsize => Zdest_src
               | Zpop       of Zrm
               | Zpush      of Zimm_rm
               | Zcall      of Zimm_rm
               | Zret       of word64
               | Zmov       of Zcond => Zsize => Zdest_src
               | Zmovzx     of Zsize => Zdest_src => Zsize
               | Zjcc       of Zcond => word64    (* jcc includes jmp rel, i.e. unconditional relative jumps. *)
               | Zjmp       of Zrm                (* jmp excludes relative jumps, see jcc. *)
               | Zloop      of Zcond => word64    (* Here Zcond over approximates possibilities. *)`;

(* This semantics understands the following prefixes in addition to the REX prefix. *)
val _ = Hol_datatype `Zprefix = Zlock
                              | Zbranch_taken
                              | Zbranch_not_taken
                              | Zoperand_size_override `;

val Zprefix_group_def = Define `
  (Zprefix_group Zlock = 1) /\
  (Zprefix_group Zbranch_taken = 2) /\
  (Zprefix_group Zbranch_not_taken = 2) /\
  (Zprefix_group Zoperand_size_override = 3)`;

val _ = Hol_datatype `Zinst = Zfull_inst of Zprefix list => Zinstruction`;


val _ = export_theory ();
