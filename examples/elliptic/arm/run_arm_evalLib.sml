(* ========================================================================= *)
(* FILE          : run_arm_evalLib.sml                                       *)
(* DESCRIPTION   : Examples using arm_evalLib                                *)
(*                                                                           *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2005-2006                                                 *)
(* ========================================================================= *)

(* interactive use:
  load "arm_evalLib";
*)

open HolKernel boolLib bossLib;
open arm_evalLib;

val max = valOf Int.maxInt;

(* ------------------------------------------------------------------------- *)

(* Assemble a rudimentary exception handler *)

val mem = list_assemble ``(\x. 0xE6000010w):mem``
  ["0x0: movs pc, #32",
   "label: b label",
   "movs pc, r14",
   "subs pc, r14, #4",
   "subs pc, r14, #8",
   "movs pc, r14",
   "subs pc, r14, #4",
   "subs pc, r14, #4"];

(* val _ = save_mem "handler" Arbnum.zero (Arbnum.fromInt 7) false mem; *)

(* Initial general purpose register values *)

val reg = set_registers ``(\x. 0w):reg``
 ``[(r0,0w);  (r1,0w);  (r2,0w);  (r3,0w);
    (r4,0w);  (r5,0w);  (r6,0w);  (r7,0w);
    (r8,0w);  (r9,0w);  (r10,0w); (r11,0w);
    (r12,0w); (r13,0w); (r14,0w); (r15,0x8000w);
    (r8_fiq,0w); (r9_fiq,0w); (r10_fiq,0w); (r11_fiq,0w);
    (r12_fiq,0w); (r13_fiq,0w); (r14_fiq,0w);
    (r13_irq,0w); (r14_irq,0w);
    (r13_svc,0w); (r14_svc,0w);
    (r13_abt,0w); (r14_abt,0w);
    (r13_und,0w); (r14_und,0w)]: (register # word32) list``;

(* Initial program status register values *)

val psr = set_status_registers
 ``(\x. SET_NZCV (F,F,F,F) (SET_IFMODE F F usr 0w)):psr``
 ``[(CPSR,SET_NZCV (F,F,F,F) (SET_IFMODE F F usr 0w))]: (psrs # word32) list``;

(* ------------------------------------------------------------------------- *)

(* Load test program *)

val prog = list_assemble mem
  ["0x8000:\
  \ mov r0, #55",
   "mov r1, #99",
   "mul r3, r0, r1",
   "mla r4, r1, r3, r0"];

val res = evaluate max prog reg psr;

(* ------------------------------------------------------------------------- *)
