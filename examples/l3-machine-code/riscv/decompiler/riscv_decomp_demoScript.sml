open HolKernel Parse boolLib bossLib;
open riscv_decompLib

val () = new_theory "riscv_decomp_demo";

val () = utilsLib.add_to_the_compset ([], riscvTheory.inventory)

local
  fun assemble1 tm =
     stringSyntax.fromHOLstring
       (utilsLib.rhsc (EVAL ``word_to_hex_string (riscv$Encode ^tm)``))
in
  val assemble = utilsLib.strings_to_quote o List.map assemble1
end

fun riscv_decompile_code s = riscv_decompLib.riscv_decompile s o assemble

val (text1_cert, test1_def) = riscv_decompile_code "test1"
  [
   ``ArithI (ADDI (1w, 2w, 4w))``,
   ``MulDiv (MUL (1w, 3w, 1w))``,
   ``ArithR (ADD (2w, 1w, 1w))``
  ]

val (text2_cert, test2_def) = riscv_decompile_code "test2"
  [
   ``ArithI (ADDI (1w, 1w, -1w))``,
   ``Branch (BEQ (1w, 0w, -2w))``
  ]

val () = computeLib.add_funs [test1_def, test2_def]

val run1 = Theory.save_thm ("run1",
  EVAL ``test1 (20w, 11w)``
  )

val run2 = Theory.save_thm ("run2",
  EVAL ``test2 11w``
  )

val () = export_theory()
