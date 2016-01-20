open HolKernel Parse boolLib bossLib;
open mips_decompLib

val () = new_theory "mips_decomp_demo";

fun mips_decompile_code s =
  mips_decompLib.mips_decompile s o utilsLib.strings_to_quote o
  List.map mips.encodeInstruction o helperLib.quote_to_strings

val (text1_cert, test1_def) = mips_decompile_code "test1"
  `ori $1, $0, 10
   bne $1, $0, 0xFFFF
   daddiu $1, $1, 0xFFFF`

val (text2_cert, test2_def) = mips_decompile_code "test2"
  `ori $1, $0, 10
   beq $1, $0, 1
   nop`

(* These decompile under the assumption that arithmetic exceptions do not
   occur *)

val (text3_cert, test3_def) = mips_decompile_code "test3"
  `dadd $1, $2, $3
   dmult $1, $3`

val () = computeLib.add_funs [test1_def, test2_def, test3_def]

val run1 = Theory.save_thm("run1",
  EVAL ``test1 0w``
  )

val run2 = Theory.save_thm("run2",
  EVAL ``test2 0w``
  )

val run3 = Theory.save_thm("run3",
  EVAL ``test3 (0w, 2w, 4w)``
  )

val () = export_theory()
