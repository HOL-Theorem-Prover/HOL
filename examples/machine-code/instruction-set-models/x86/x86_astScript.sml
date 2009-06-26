
open HolKernel boolLib bossLib Parse;

open x86_coretypesTheory;

val _ = new_theory "x86_ast";


(* ---------------------------------------------------------------------------------- *>

  This theory defines the abstract syntax tree (AST) for x86 instructions. It uses 

     Ximm - type of immediate constant
     Xreg - type of register name

  from x86_coretypesTheory.

  Nearly all instructions operate only over 32-bit data.
  However, MOV, CMP and DEC are defined also for some 8-bit operations.

<* ---------------------------------------------------------------------------------- *)


val _ = Hol_datatype `
  Xrm = Xr of Xreg                                         (* register *) 
      | Xm of (word2 # Xreg) option => Xreg option => Ximm (* mem[2^{scale} * index + base + displacement] *)`;

(* check whether rm requires a lock, i.e. specifies a memory access *)

val rm_is_memory_access_def = Define `
  (rm_is_memory_access (Xm i b d) = T) /\ 
  (rm_is_memory_access (Xr r) = F)`;

val _ = Hol_datatype `
  Xdest_src = Xrm_i of Xrm  => Ximm  (* mnemonic r/m32, imm32 or mnemonic r/m32, imm8 (sign-extended) *)
            | Xrm_r of Xrm  => Xreg  (* mnemonic r/m32, r32 *)
            | Xr_rm of Xreg => Xrm   (* mnemonic r32, r/m32 *)  `;

val _ = Hol_datatype `
  Ximm_rm = Xi_rm of Xrm    (* r/m32 *) 
          | Xi    of Ximm   (* imm32 or imm8 (sign-extended) *) `;

val _ = Hol_datatype `Xbinop_name = Xadd | Xand | Xcmp | Xor | Xshl | Xshr | Xsar | Xsub | Xtest | Xxor `;
val _ = Hol_datatype `Xmonop_name = Xdec | Xinc | Xnot | Xneg `;

val _ = Hol_datatype `Xcond = (* this list is not complete *)
    X_ALWAYS            (* N = not     *)
  | X_E | X_NE          (* E = equal   *)
  | X_S | X_NS          (* S = signed  *)
  | X_A | X_NA          (* A = above   *)
  | X_B | X_NB          (* B = below   *)`;

val _ = Hol_datatype `
  Xinstruction = Xbinop     of Xbinop_name => Xdest_src
               | Xmonop     of Xmonop_name => Xrm
               | Xcmpxchg   of Xrm => Xreg 
               | Xxadd      of Xrm => Xreg 
               | Xxchg      of Xrm => Xreg 
               | Xmul       of Xrm
               | Xdiv       of Xrm
               | Xlea       of Xdest_src
               | Xpop       of Xrm
               | Xpush      of Ximm_rm
               | Xcall      of Ximm_rm
               | Xret       of Ximm
               | Xmov       of Xcond => Xdest_src
               | Xmov_byte  of Xdest_src          
               | Xcmp_byte  of Xdest_src
               | Xdec_byte  of Xrm
               | Xjcc       of Xcond => Ximm      (* jcc includes jmp rel, i.e. unconditional relative jumps. *)
               | Xjmp       of Xrm                (* jmp excludes relative jumps, see jcc. *)
               | Xloop      of Xcond => Ximm      (* Here Xcond over approximates possibilities. *)
               | Xpushad      
               | Xpopad     `;

val _ = Hol_datatype `Xpre_g1 = Xlock | Xg1_none `;
val _ = Hol_datatype `Xpre_g2 = Xbranch_taken | Xbranch_not_taken | Xg2_none `;

val _ = Hol_datatype `Xinst = Xprefix of Xpre_g1 => Xpre_g2 => Xinstruction`;


val _ = export_theory ();
