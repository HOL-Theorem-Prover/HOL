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
   "daddiu $1, $1, 10"
  ]

List.map mips.encodeInstruction
  [
   "ori $1, $0, 10",
   "beq $1, $0, 1",
   "nop",
   "nop"
  ]

val test_def = mips_decompile "test"
   `3401000A
    10200001 00000000
    00000000`


val q = (helperLib.quote_to_strings: term quotation -> string list)
val tools = mips_tools
val name = "test"
val fio = NONE: (term * term) option
val code =
   `3401000A
    10200001 00000000
    00000000`

val MIPS_PC_SIMP = prove(
  ``(r * MIPS_PC pc * cond ((1 >< 0) pc = 0w:word2) = r * MIPS_PC pc) /\
    (MIPS_PC pc * cond ((1 >< 0) pc = 0w:word2) = MIPS_PC pc)``,
  FULL_SIMP_TAC (std_ss++sep_cond_ss) [mips_progTheory.MIPS_PC_def]);

local
  val f = #1 mips_tools
  fun map_inst r ((th1,x1,x2),NONE) = ((r th1,x1,x2),NONE)
    | map_inst r ((th1,x1,x2),SOME (th2,y1,y2)) =
        ((r th1,x1,x2),SOME (r th2,y1,y2))
in
  val new_mips_tools =
    (map_inst (REWRITE_RULE [MIPS_PC_SIMP]) o f,
     #2 mips_tools, #3 mips_tools, #4 mips_tools)
end

val res = decompilerLib.decompile new_mips_tools "test"
   `3401000A
    10200001 00000000
    00000000`

*)

end
