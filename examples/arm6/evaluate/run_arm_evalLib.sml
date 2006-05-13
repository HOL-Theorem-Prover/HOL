(* ========================================================================= *)
(* FILE          : run_arm_evalLib.sml                                       *)
(* DESCRIPTION   : Examples using arm_evalLib                                *)
(*                                                                           *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2005-2006                                                 *)
(* ========================================================================= *)

(* interactive use:
  app load ["arm_evalLib"];
*)

open HolKernel boolLib bossLib;
open arm_evalLib;

val max = valOf Int.maxInt;

(* ------------------------------------------------------------------------- *)

(* Assemble a rudimentary exception handler *)

val mem = list_assemble ``(\x. 0xE6000010w):mem``
  ["0x0: movs pc, #32",
   "b 0",
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
    (r12,0w); (r13,0w); (r14,0w); (r15,0x20w);
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

val prog = assemble ``(\x. 0w):mem`` "test.s";

(* Testing/Examples *)

(* To execute machine code...
val compile = rhs o concl o ARM_ASSEMBLE_CONV;
val mem = compile mem;
*)

val prog = list_assemble mem
  ["0x20:\
   \mov r0, #0xFF00",
   "mov r1, #37",
   "str r1, [r0], #4",
   "ldr r2, [r0, #-4]!"];

val res = evaluate max prog reg psr;

val prog1 = assemble1 mem "0x20: mov r0, #1";

val res1 = evaluate max prog1 reg psr;

val prog2 = list_assemble mem
  ["0x20:\
   \mov r0, #12",
   "mov r1, #10",
   "eor r2, r0, r1",
   "and r3, r0, r1",
   "orr r4, r0, r1",
   "bic r5, r0, r1"];

val res2 = evaluate max prog2 reg psr;

val prog3 = list_assemble mem
  ["0x20: mov r0, #10",
   "0x24: add r0, r0, #1",
   "      cmp r0, #12",
   "      bne 0x24"];

val res3 = evaluate max prog3 reg psr;

val prog4 = list_assemble mem
  ["0x20:\
   \mov r0, #0xF",
   "mov r1, #4",
   "mvn r2, r0, lsl r1",
   "add r3, r3, r0, lsl #8",
   "mov r4, r0, ror #4",
   "mov r5, r4, lsr #4",
   "mov r6, r4, asr #16"];

val res4 = evaluate max prog4 reg psr;

val prog5 = list_assemble mem
  ["0x20:\
   \mov r0, #0xF",
   "mov r1, #4",
   "mvn r2, r0, lsl r1",
   "add r3, r3, r0, lsl #8",
   "mov r4, r0, ror #4",
   "mov r5, r4, lsr #4",
   "mov r6, r4, asr #16"];

val res5 = evaluate max prog5 reg psr;

val prog6 = list_assemble mem
  ["0x20:\
   \mov r0, #8",
   "mov r1, #12",
   "mul r2, r0, r1",
   "mla r3, r2, r1, r2"];

val res6 = evaluate max prog6 reg psr;

val prog7 = list_assemble mem
  ["0x20:\
   \mov  r0, #0xFF",
   "mul  r0, r0, r0",
   "str  r0, [r0], #4",
   "strb r0, [r0]",
   "ldr  r1, [r0]",
   "ldrb r2, [r3]"];

val res7 = evaluate max prog7 reg psr;

val prog8 = list_assemble mem
  ["0x20:\
   \ldmia r0, {r1-r10}",
   "stmdb r1, {r1-r10}"];

val res8 = evaluate max prog8 reg psr;

val prog9 = list_assemble mem
  ["0x20:\
   \mov  r0, #77",
   "mov  r1, #88",
   "mov  r2, #0xF00",
   "swp  r0, r1, [r2]",
   "swpb r3, r1, [r0]"];

val res9 = evaluate max prog9 reg psr;

val prog10 = list_assemble ``(\x. 0xE6000010w):mem``
  ["mrs r0, CPSR",
   "mrs r1, SPSR",
   "mov r2, #0xF0000000",
   "orr r2, r2, #0x12",
   "msr CPSR, r2",
   "msr SPSR_c, r2"];

val res10 = evaluate 6 prog10 ``(\x. 0w):reg`` psr;

(* ------------------------------------------------------------------------- *)
