open HolKernel Parse boolLib bossLib;
open m0_decompLib

val () = new_theory "m0_decomp_demo";

(* test program *)
val q =
   `movs r1, #0              ; accumulator
    mov  r3, r0              ; first address
    adds r3, #40             ; last address (10 loads)
l1: ldr  r2, [r0, #4]        ; load data
    adds r0, #4              ; increment address
    add  r1, r2              ; add to accumulator
    cmp  r0, r3              ; test if done
    blt  l1                  ; loop if not done`

(* from GAS *)
val (test_cert, test_def) = m0_decompile "test" `
   2100
   0003
   3328
   6842
   3004
   4411
   4298
   DBFA`

(* internal assembler *)
val () = m0AssemblerLib.print_m0_code q

val (test2_cert, test2_def) = m0_decompile_code "test2" q

val () = computeLib.add_funs [test_def]
val () = computeLib.add_funs [test2_def]

val run1 = Theory.save_thm("run1",
  EVAL ``test (12w, 0, dmem, \a. if a && 3w = 0w then 4w else 0w)``)

val run2 = Theory.save_thm("run2",
  EVAL ``test2 (12w, 0, dmem, \a. if a && 3w = 0w then 4w else 0w)``)

val () = export_theory()
