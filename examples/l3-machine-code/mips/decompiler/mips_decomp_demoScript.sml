open HolKernel Parse boolLib bossLib;
open mips_decompLib

val () = new_theory "mips_decomp_demo";

fun mips_decompile_code s =
  mips_decompLib.mips_decompile s o utilsLib.strings_to_quote o
  List.map mips.encodeInstruction o helperLib.quote_to_strings

val (test1_cert, test1_def) = mips_decompile_code "test1"
  `ori $r1, $r0, 10
   bne $r1, $r0, 0x3FFFC
   daddiu $r1, $r1, 0xFFFF`

val (test2_cert, test2_def) = mips_decompile_code "test2"
  `ori $r1, $r0, 10
   beq $r1, $r0, 4
   nop`

(* These decompile under the assumption that arithmetic exceptions do not
   occur *)

val (test3_cert, test3_def) = mips_decompile_code "test3"
  `dadd $r1, $r2, $r3
   dmult $r1, $r3`

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
