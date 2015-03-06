structure mips_decompLib :> mips_decompLib =
struct

open HolKernel Parse boolLib bossLib
open helperLib set_sepTheory addressTheory progTheory
open pred_setTheory combinTheory
open mips_progLib decompilerLib

val ERR = Feedback.mk_HOL_ERR "mips_decompLib"

(* automation *)

local
   fun format_thm th =
      let
         val c = progSyntax.dest_code (Thm.concl th)
         val n = List.length (pred_setSyntax.strip_set c) * 4
      in
         (th, n,
          stateLib.get_pc_delta
             (Lib.equal "mips_prog$MIPS_PC" o fst o
              boolSyntax.dest_strip_comb) th)
      end
in
   fun format_mips_spec hex =
      case List.map format_thm (mips_progLib.mips_spec_hex2 hex) of
         [x] => (x, NONE)
       | [x1, x2] => (x1, SOME x2)
       | _ => raise ERR "format_mips_spec" ""
end

val mips_pc = Term.prim_mk_const {Thy = "mips_prog", Name = "MIPS_PC"}

val mips_tools =
   (format_mips_spec, fn _ => fail(), TRUTH, mips_pc): decompiler_tools

val mips_decompile = decompilerLib.decompile mips_tools

(* testing and debugging

open mips_decompLib

List.map mips.encodeInstruction
  [
   "ori $1, $0, 10",
   "bne $1, $0, 0xFFFF",
   "daddiu $1, $1, 0xFFFF"
  ]

val (text_cert, test_def) = mips_decompile "test"
   `3401000A
    1420FFFF 6421FFFF`

val () = computeLib.add_funs [test_def]

EVAL ``test 0w``

List.map mips.encodeInstruction
  [
   "ori $1, $0, 10",
   "beq $1, $0, 1"
  ]

val test_def = mips_decompile "test"
   `3401000A
    10200001 00000000`

*)

end
