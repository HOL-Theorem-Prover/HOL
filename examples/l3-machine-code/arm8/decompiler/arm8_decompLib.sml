structure arm8_decompLib :> arm8_decompLib =
struct

open HolKernel Parse boolLib bossLib
open decompilerLib arm8_progLib

val ERR = Feedback.mk_HOL_ERR "arm8_decompLib"

local
   fun w_var i = Term.mk_var ("w" ^ Int.toString i, ``:word32``)
   fun word32 w = wordsSyntax.mk_wordi (Arbnum.fromHexString w, 32)
   fun format_thm th =
      (th, 4,
       stateLib.get_pc_delta
          (Lib.equal "arm8_prog$arm8_pc" o fst o boolSyntax.dest_strip_comb) th)
in
   fun arm8_triples hex =
      case String.tokens (fn c => c = #" ") hex of
         h :: r =>
           let
              val ws = List.tabulate (List.length r, w_var)
              val l =
                List.map (fn (v, hx) => v |-> word32 hx) (ListPair.zip (ws, r))
           in
              List.map (Thm.INST l)
                 (stateLib.fix_precond (arm8_progLib.arm8_spec_hex h))
           end
       | _ => raise ERR "arm8_triples" "empty string"
   fun arm8_spec hex =
      case List.map format_thm (arm8_triples hex) of
         [x] => (x, NONE)
       | [x1, x2] => (x1, SOME x2)
       | _ => raise ERR "arm8_spec" ""
   fun arm8_spec_opt s hex = (arm8_progLib.arm8_config s; arm8_spec hex)
end

val arm8_pc = Term.prim_mk_const {Thy = "arm8_prog", Name = "arm8_pc"}

fun gen_arm8_tools f hide = (f, fn _ => fail(), hide, arm8_pc): decompiler_tools
fun arm8_tools_opt opt = gen_arm8_tools (arm8_spec_opt opt)

val arm8_tools = gen_arm8_tools arm8_spec arm8_progTheory.aS_HIDE
val arm8_tools_no_status = gen_arm8_tools arm8_spec TRUTH
val arm8_tools_array = arm8_tools_opt "array" arm8_progTheory.aS_HIDE
val arm8_tools_array_no_status = arm8_tools_opt "array" TRUTH
val arm8_tools_map8 = arm8_tools_opt "map8" arm8_progTheory.aS_HIDE
val arm8_tools_map8_no_status = arm8_tools_opt "map8" TRUTH
val arm8_tools_map32 = arm8_tools_opt "map32" arm8_progTheory.aS_HIDE
val arm8_tools_map32_no_status = arm8_tools_opt "map32" TRUTH

fun gen_arm8_decompile iscode tools opt name (qcode: string quotation) =
   let
      val q = if iscode then arm8AssemblerLib.arm8_code
              else arm8AssemblerLib.arm8_code
      val decomp = decompilerLib.decompile_with q tools
   in
      arm8_progLib.arm8_config opt
    ; (decompilerLib.UNABBREV_CODE_RULE ## I) (decomp name qcode)
   end

val arm8_decompile = gen_arm8_decompile false arm8_tools "map8"
val arm8_decompile_no_status =
   gen_arm8_decompile false arm8_tools_no_status "map8"
val arm8_decompile32 = gen_arm8_decompile false arm8_tools "map32"
val arm8_decompile32_no_status =
   gen_arm8_decompile false arm8_tools_no_status "map32"

val arm8_decompile_code = gen_arm8_decompile true arm8_tools "map8"
val arm8_decompile_code_no_status =
   gen_arm8_decompile true arm8_tools_no_status "map8"
val arm8_decompile32_code = gen_arm8_decompile true arm8_tools "map32"
val arm8_decompile32_code_no_status =
   gen_arm8_decompile true arm8_tools_no_status "map32"

(* testing

open arm8_decompLib

val (test_cert, test_def) = arm8_decompile_no_status "test"
   `54000048
    1b000001
    `

val (test_cert, test_def) = arm8_decompile_code_no_status "test"
   `mov x1, #4
    add x2, x3, x4
    str x2, [x1, #8]!
    `

val (ex_cert, ex_def) = arm8_decompLib.arm8_decompile_code "ex"
  `loop: mul  x1, x1, x2
         subs x0, x0, #1
         b.ne  loop`

*)

end
