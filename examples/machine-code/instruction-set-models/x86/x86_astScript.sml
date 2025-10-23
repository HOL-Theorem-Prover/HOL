
Theory x86_ast
Ancestors
  x86_coretypes

(* ---------------------------------------------------------------------------------- *>

  This theory defines the abstract syntax tree (AST) for x86 instructions. It uses

     Ximm - type of immediate constant
     Xreg - type of register name

  from x86_coretypesTheory.

  Nearly all instructions operate only over 32-bit data.
  However, MOV, CMP and DEC are defined also for some 8-bit operations.

<* ---------------------------------------------------------------------------------- *)


Datatype:
  Xrm = Xr Xreg                                         (* register *)
      | Xm ((word2 # Xreg) option) (Xreg option) Ximm (* mem[2^{scale} * index + base + displacement] *)
End

(* check whether rm requires a lock, i.e. specifies a memory access *)

Definition rm_is_memory_access_def:
  (rm_is_memory_access (Xm i b d) = T) /\
  (rm_is_memory_access (Xr r) = F)
End

Datatype:
  Xdest_src = Xrm_i Xrm  Ximm  (* mnemonic r/m32, imm32 or mnemonic r/m32, imm8 (sign-extended) *)
            | Xrm_r Xrm  Xreg  (* mnemonic r/m32, r32 *)
            | Xr_rm Xreg Xrm   (* mnemonic r32, r/m32 *)
End

Datatype:
  Ximm_rm = Xi_rm Xrm    (* r/m32 *)
          | Xi    Ximm   (* imm32 or imm8 (sign-extended) *)
End

Datatype: Xbinop_name = Xadc | Xadd | Xand | Xcmp | Xor | Xshl | Xshr | Xsar | Xsub | Xsbb | Xtest | Xxor
End
Datatype: Xmonop_name = Xdec | Xinc | Xnot | Xneg
End

Datatype: Xcond = (* this list is not complete *)
    X_ALWAYS            (* N = not     *)
  | X_E | X_NE          (* E = equal   *)
  | X_S | X_NS          (* S = signed  *)
  | X_A | X_NA          (* A = above   *)
  | X_B | X_NB          (* B = below   *)
End

Datatype:
  Xinstruction = Xbinop     Xbinop_name Xdest_src
               | Xmonop     Xmonop_name Xrm
               | Xcmpxchg   Xrm Xreg
               | Xxadd      Xrm Xreg
               | Xxchg      Xrm Xreg
               | Xmul       Xrm
               | Xdiv       Xrm
               | Xlea       Xdest_src
               | Xpop       Xrm
               | Xpush      Ximm_rm
               | Xcall      Ximm_rm
               | Xret       Ximm
               | Xmov       Xcond Xdest_src
               | Xmovzx     Xdest_src
               | Xmov_byte  Xdest_src
               | Xcmp_byte  Xdest_src
               | Xdec_byte  Xrm
               | Xjcc       Xcond Ximm      (* jcc includes jmp rel, i.e. unconditional relative jumps. *)
               | Xjmp       Xrm                (* jmp excludes relative jumps, see jcc. *)
               | Xloop      Xcond Ximm      (* Here Xcond over approximates possibilities. *)
               | Xpushad
               | Xpopad
End

Datatype: Xpre_g1 = Xlock | Xg1_none
End
Datatype: Xpre_g2 = Xbranch_taken | Xbranch_not_taken | Xg2_none
End

Datatype: Xinst = Xprefix Xpre_g1 Xpre_g2 Xinstruction
End
