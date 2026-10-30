Theory riscv_decomp_demo
Ancestors
  riscv_prog
Libs
  riscv_decompLib

val () =
  utilsLib.add_to_the_compset ([], Import.gen_inventory {thyname="riscv"})

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

fun riscv_decompile_code_noC s = riscv_decompLib.riscv_decompile_noC s o assemble

val (text3_cert, test3_def) = riscv_decompile_code_noC "test3"
  [
   ``ArithI (ADDI (1w, 1w, -1w))``,
   ``Branch (BEQ (1w, 0w, -2w))``
  ]

val (text4_cert, test4_def) = riscv_decompile_code_noC "test4"
  [
   ``ArithI (ADDI (1w, 1w, 1w))``,
   ``Branch (BEQ (0w, 0w, 4w))``,
   ``ArithI (ADDI (1w, 1w, 1w))``,
   ``Branch (JAL (0w, 4w))``,
   ``ArithI (ADDI (1w, 1w, 1w))``,
   ``ArithI (ADDI (2w, 1w, 0w))``
  ]

(* Data accesses.  The M-mode contract of their step theorems (H1 to H4 and
   H6, riscv_stepTheory) is part of riscv_RV64I, so the certificates assume
   only that the address is aligned (H5) and the data are in dmem.  test5
   accesses 8 bytes, which needs H4 (every PMP entry OFF or NAPOT), test6 4
   bytes, which does not, and test7 is an AMO, which reads and writes. *)

val (text5_cert, test5_def) = riscv_decompile_code "test5"
  [
   ``Load (LD (2w, 1w, 0w))``,
   ``ArithI (ADDI (2w, 2w, 1w))``,
   ``Store (SD (1w, 2w, 0w))``
  ]

val (text6_cert, test6_def) = riscv_decompile_code_noC "test6"
  [
   ``Load (LW (2w, 1w, 8w))``,
   ``ArithR (ADD (2w, 2w, 3w))``,
   ``Store (SW (1w, 2w, 8w))``
  ]

val (text7_cert, test7_def) = riscv_decompile_code "test7"
  [
   ``AMO (AMOADD_W (0w, 0w, 2w, 1w, 3w))``,
   ``ArithR (ADD (2w, 2w, 3w))``
  ]

val () = computeLib.add_funs [test1_def, test2_def]

val run1 = Theory.save_thm ("run1",
  EVAL ``test1 (20w, 11w)``
  )

val run2 = Theory.save_thm ("run2",
  EVAL ``test2 11w``
  )
