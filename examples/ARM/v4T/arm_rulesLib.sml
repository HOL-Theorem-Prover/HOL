(* ========================================================================= *)
(* FILE          : arm_rulesLib.sml                                          *)
(* DESCRIPTION   : Tools for symbolic evaluation of the ARM Instruction Set  *)
(*                                                                           *)
(* AUTHORS       : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2006                                                      *)
(* ========================================================================= *)

structure arm_rulesLib :> arm_rulesLib =
struct

(* interactive use:
  app load ["instructionSyntax", "arm_rulesTheory"];
*)

open HolKernel boolLib Parse bossLib;
open Q wordsTheory arm_evalTheory;

(* ------------------------------------------------------------------------- *)

val SIMP_USR = SIMP_RULE bool_ss [armTheory.USER_def];

val ARM_PSR_ss = rewrites
  [SIMP_USR SPSR_READ_THM2, SIMP_USR SPSR_WRITE_THM, SIMP_USR SPSR_WRITE_READ,
   SPSR_WRITE_WRITE, CPSR_WRITE_READ, CONJUNCT1 CPSR_READ_WRITE,
   CPSR_WRITE_WRITE, PSR_WRITE_COMM, SPSR_READ_WRITE, armTheory.mode_distinct,
   SET_NZCV_ID, DECODE_IFTM_SET_NZCV, DECODE_NZCV_SET_NZCV,
   DECODE_IFTM_SET_IFTM, DECODE_NZCV_SET_IFTM, SET_NZCV_IDEM,
   SET_IFTM_IDEM, SET_IFTM_NZCV_SWP];

val ARM_REG_ss = rewrites
  [FETCH_PC, INC_PC, REG_WRITE_FETCH_PC, FETCH_PC_REG_WRITE, FETCH_PC_INC_PC,
   REG_WRITE_READ, REG_READ_WRITE, REG_WRITE_INC_PC, REG_READ_INC_PC,
   INC_PC_REG_WRITE, REG_WRITE_WRITE];

val PSR_CONV = SIMP_CONV (pure_ss++ARM_PSR_ss) [];

(* ------------------------------------------------------------------------- *)


end
