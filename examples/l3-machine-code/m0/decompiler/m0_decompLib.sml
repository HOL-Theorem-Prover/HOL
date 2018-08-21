structure m0_decompLib :> m0_decompLib =
struct

open HolKernel Parse boolLib bossLib
open decompilerLib m0_progLib m0_progTheory m0_decompTheory

val () = m0_progLib.set_newline ""

val ERR = mk_HOL_ERR "m0_decompLib"

local
   fun get_length th =
      if sumSyntax.is_inl (m0_progLib.get_code th) then 2 else 4
   val find_exit =
      stateLib.get_pc_delta
          (Lib.equal "m0_prog$m0_PC" o fst o boolSyntax.dest_strip_comb)
   fun format_thm th = (th, get_length th, find_exit th)
   val count_INTRO_rule =
      stateLib.introduce_triple_definition (false, m0_COUNT_def) o
      Thm.INST [``endianness:bool`` |-> boolSyntax.F,
                ``spsel:bool`` |-> boolSyntax.F]
   val finalise =
      List.map format_thm o stateLib.fix_precond o List.map count_INTRO_rule
in
   val set_opt = m0_progLib.m0_config false
   fun m0_triples hex =
      case finalise (m0_progLib.m0_spec_hex hex) of
         [x] => (x, NONE)
       | [x1, x2] => (x1, SOME x2)
       | _ => raise ERR "m0_triples" ""
   fun m0_triples_opt s hex = (set_opt s; m0_triples hex)
end

val m0_pc = Term.prim_mk_const {Thy = "m0_prog", Name = "m0_PC"}

fun m0_tools f hide = (f, fn _ => fail(), hide, m0_pc): decompiler_tools
fun m0_tools_opt opt = m0_tools (m0_triples_opt opt)

val l3_m0_tools = m0_tools m0_triples m0_NZCV_HIDE
val l3_m0_tools_no_status = m0_tools m0_triples TRUTH

val l3_m0_tools_flat = m0_tools_opt "flat" m0_NZCV_HIDE
val l3_m0_tools_array = m0_tools_opt "array" m0_NZCV_HIDE
val l3_m0_tools_mapped = m0_tools_opt "mapped" m0_NZCV_HIDE

val l3_m0_tools_flat_no_status = m0_tools_opt "flat" TRUTH
val l3_m0_tools_array_no_status = m0_tools_opt "array" TRUTH
val l3_m0_tools_mapped_no_status = m0_tools_opt "mapped" TRUTH

fun m0_decompile name qcode =
   (set_opt "mapped"; decompilerLib.decompile l3_m0_tools name qcode)

fun m0_decompile_code name (qass: string quotation) =
   ( set_opt "mapped"
   ; decompilerLib.decompile_with m0AssemblerLib.m0_code l3_m0_tools name qass
   )

end
