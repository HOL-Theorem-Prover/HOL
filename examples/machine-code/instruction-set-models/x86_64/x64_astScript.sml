
Theory x64_ast
Ancestors
  x64_coretypes

(* ---------------------------------------------------------------------------------- *>

  This theory defines the abstract syntax tree (AST) for x64 instructions. It uses

     word64 - type of immediate constant
     Zreg - type of register name

  from x64_coretypesTheory.

<* ---------------------------------------------------------------------------------- *)


Datatype:
  Zrm = Zr Zreg                                         (* register *)
      | Zm ((word2 # Zreg) option) (Zreg option) word64 (* mem[2^{scale} * index + base + displacement] *)
End

(* check whether rm requires a lock, i.e. specifies a memory access *)

Definition Zrm_is_memory_access_def:
  (Zrm_is_memory_access (Zm i b d) = T) /\
  (Zrm_is_memory_access (Zr r) = F)
End

Datatype:                  (* Here XX is one of 8, 16, 32, 64. *)
  Zdest_src = Zrm_i Zrm  word64  (* mnemonic r/mXX, immXX (sign-extended) *)
            | Zrm_r Zrm  Zreg    (* mnemonic r/mXX, rXX *)
            | Zr_rm Zreg Zrm     (* mnemonic rXX, r/mXX *)
End

Datatype:
  Zimm_rm = Zi_rm Zrm      (* r/mXX *)
          | Zi    word64   (* sign-extended immediate *)
End

Datatype: Zbinop_name = Zadc | Zadd | Zand | Zcmp | Zor | Zshl | Zshr | Zsar | Zsub | Zsbb | Ztest | Zxor
End
Datatype: Zmonop_name = Zdec | Zinc | Znot | Zneg
End

Datatype: Zcond = (* this list is not complete *)
    Z_ALWAYS            (* N = not     *)
  | Z_E | Z_NE          (* E = equal   *)
  | Z_S | Z_NS          (* S = signed  *)
  | Z_A | Z_NA          (* A = above   *)
  | Z_B | Z_NB          (* B = below   *)
End

Datatype:
  Zinstruction = Zbinop     Zbinop_name Zsize Zdest_src
               | Zmonop     Zmonop_name Zsize Zrm
               | Zcmpxchg   Zsize Zrm Zreg
               | Zxadd      Zsize Zrm Zreg
               | Zxchg      Zsize Zrm Zreg
               | Zmul       Zsize Zrm
               | Zdiv       Zsize Zrm
               | Zlea       Zsize Zdest_src
               | Zpop       Zrm
               | Zpush      Zimm_rm
               | Zcall      Zimm_rm
               | Zret       word64
               | Zcpuid
               | Zmov       Zcond Zsize Zdest_src
               | Zmovzx     Zsize Zdest_src Zsize
               | Zjcc       Zcond word64    (* jcc includes jmp rel, i.e. unconditional relative jumps. *)
               | Zjmp       Zrm                (* jmp excludes relative jumps, see jcc. *)
               | Zloop      Zcond word64    (* Here Zcond over approximates possibilities. *)
End

(* This semantics understands the following prefixes in addition to the REX prefix. *)
Datatype: Zprefix = Zlock
                              | Zbranch_taken
                              | Zbranch_not_taken
                              | Zoperand_size_override
End

Definition Zprefix_group_def:
  (Zprefix_group Zlock = 1) /\
  (Zprefix_group Zbranch_taken = 2) /\
  (Zprefix_group Zbranch_not_taken = 2) /\
  (Zprefix_group Zoperand_size_override = 3)
End

Datatype: Zinst = Zfull_inst (Zprefix list) Zinstruction
End
