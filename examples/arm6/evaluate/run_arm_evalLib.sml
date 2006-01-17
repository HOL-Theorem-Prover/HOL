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

(* ------------------------------------------------------------------------- *)

val zero = Arbnum.zero;
val max = valOf Int.maxInt;

(* A selection of instructions, encoded in HOL *)

val l = [
  `B AL 4w`,
  `BL EQ ($- 4w)`,
  `ADD CS F 4w 3w (Dp_immediate 0w 5w)`,
  `AND VS T 4w 3w (Dp_shift_immediate (LSL 2w) 0w)`,
  `TST AL 4w (Dp_shift_immediate (LSL 2w) 1w)`,
  `MOV AL F 4w (Dp_shift_immediate (ASR 2w) 0w)`,
  `MVN AL T 4w (Dp_shift_immediate (ROR 2w) 0w)`,
  `RSC AL F 4w 3w (Dp_shift_register (LSL 2w) 1w)`,
  `MRS AL F 1w`,
  `MRS AL T 1w`,
  `MSR AL CPSR_f (Msr_immediate 2w 5w)`,
  `MSR AL CPSR_c (Msr_immediate 2w 5w)`,
  `MSR AL SPSR_a (Msr_immediate 2w 5w)`,
  `MSR AL SPSR_a (Msr_register 5w)`,
  `MUL AL T 4w 3w 2w`,
  `MLA AL F 4w 3w 2w 1w`,
  `LDR AL <|Pre := F;Up := F;BS := F;Wb := F|> 4w 3w (Dt_immediate 0w)`,
  `LDR AL <|Pre := F;Up := F;BS := T;Wb := T|> 4w 3w (Dt_immediate 4w)`,
  `LDR AL <|Pre := T;Up := T;BS := T;Wb := T|> 4w 3w (Dt_immediate 4w)`,
  `LDR AL <|Pre := F;Up := F;BS := F;Wb := F|> 4w 3w
          (Dt_shift_immediate (LSL 2w) 0w)`,
  `LDR AL <|Pre := F;Up := F;BS := F;Wb := F|> 4w 3w
          (Dt_shift_immediate (ROR 2w) 0w)`,
  `STR AL <|Pre := F;Up := F;BS := F;Wb := F|> 4w 3w
          (Dt_shift_immediate (LSL 2w) 4w)`,
  `STR AL <|Pre := T;Up := T;BS := T;Wb := T|> 4w 3w
          (Dt_shift_immediate (LSL 2w) 4w)`,
  `LDM AL <|Pre := T;Up := T;BS := T;Wb := T|> 4w 0xF0FFw`,
  `STM AL <|Pre := F;Up := F;BS := F;Wb := F|> 4w 0x8000w`,
  `SWP AL F 3w 2w 1w`,
  `SWP AL T 3w 2w 1w`,
  `SWI AL`,
  `UND AL`
];

val hol_prog = hol_assemble ``\x:word30. 0w:word32`` zero l;

(* translate into ARM assembly code *)

fun printn s = print (s ^ "\n");

val _ = map printn (disassemble (length l) hol_prog zero);

(* ------------------------------------------------------------------------- *)

(* Assemble a rudimentary exception handler *)

val mem = assemble ``\x:word30. 0xE6000010w:word32`` zero
  ["movs pc, #32",
   "label: b label",
   "movs pc, r14",
   "subs pc, r14, #4",
   "subs pc, r14, #8",
   "movs pc, r14",
   "subs pc, r14, #4",
   "subs pc, r14, #4"];

(*
val EXC_HANDLER = "handler";
val _ = save_mem EXC_HANDLER zero (Arbnum.fromInt 7) false mem;
*)

(* Initial general purpose register values *)

val reg = set_registers ``(\x. 0w):reg``
 ``[(r0,0w);  (r1,0w);  (r2,0w);  (r3,0w);
    (r4,0w);  (r5,0w);  (r6,0w);  (r7,0w);
    (r8,0w);  (r9,0w);  (r10,0w); (r11,0w);
    (r12,0w); (r13,0w); (r14,0w); (r15,32w);
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

(* Testing/Examples *)

val prog = assemble mem (Arbnum.fromInt 8)
  ["mov r0, #0xFF00",
   "mov r1, #37",
   "str r1, [r0], #4",
   "ldr r2, [r0, #-4]!"];

val res = evaluate max prog reg psr;

val prog1 = assemble1 mem (Arbnum.fromInt 8) "mov r0, #1";

val res1 = evaluate max prog1 reg psr;

val prog2 = assemble mem (Arbnum.fromInt 8)
  ["mov r0, #12",
   "mov r1, #10",
   "eor r2, r0, r1",
   "and r3, r0, r1",
   "orr r4, r0, r1",
   "bic r5, r0, r1"];

val res2 = evaluate max prog2 reg psr;

val prog3 = assemble mem (Arbnum.fromInt 8)
  [       "mov r0, #10",
   "label: add r0, r0, #1",
          "cmp r0, #12",
          "bne label"];

val res3 = evaluate max prog3 reg psr;

val prog4 = assemble mem (Arbnum.fromInt 8)
  ["mov r0, #0xF",
   "mov r1, #4",
   "mvn r2, r0, lsl r1",
   "add r3, r3, r0, lsl #8",
   "mov r4, r0, ror #4",
   "mov r5, r4, lsr #4",
   "mov r6, r4, asr #16"];

val res4 = evaluate max prog4 reg psr;

val prog5 = assemble mem (Arbnum.fromInt 8)
  ["mov r0, #0xF",
   "mov r1, #4",
   "mvn r2, r0, lsl r1",
   "add r3, r3, r0, lsl #8",
   "mov r4, r0, ror #4",
   "mov r5, r4, lsr #4",
   "mov r6, r4, asr #16"];

val res5 = evaluate max prog5 reg psr;

val prog6 = assemble mem (Arbnum.fromInt 8)
  ["mov r0, #8",
   "mov r1, #12",
   "mul r2, r0, r1",
   "mla r3, r2, r1, r2"];

val res6 = evaluate max prog6 reg psr;

val prog7 = assemble mem (Arbnum.fromInt 8)
  ["mov  r0, #0xFF",
   "mul  r0, r0, r0",
   "str  r0, [r0], #4",
   "strb r0, [r0]",
   "ldr  r1, [r0]",
   "ldrb r2, [r3]"];

val res7 = evaluate max prog7 reg psr;

val prog8 = assemble mem (Arbnum.fromInt 8)
  ["ldmia r0, {r1-r10}",
   "stmdb r1, {r1-r10}"];

val res8 = evaluate max prog8 reg psr;

val prog9 = assemble mem (Arbnum.fromInt 8)
  ["mov  r0, #77",
   "mov  r1, #88",
   "mov  r2, #0xF00",
   "swp  r0, r1, [r2]",
   "swpb r3, r1, [r0]"];

val res9 = evaluate max prog9 reg psr;

val prog10 = assemble ``\x:word30. 0xE6000010w:word32`` zero
  ["mrs r0, CPSR",
   "mrs r1, SPSR",
   "mov r2, #0xF0000000",
   "orr r2, r2, #0x12",
   "msr CPSR, r2",
   "msr SPSR_c, r2"];

val res10 = evaluate 6 prog10 reg psr;

(* ------------------------------------------------------------------------- *)
