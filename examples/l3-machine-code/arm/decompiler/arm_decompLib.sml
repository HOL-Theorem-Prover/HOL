structure arm_decompLib :> arm_decompLib =
struct

open HolKernel Parse boolLib bossLib;
open helperLib set_sepTheory addressTheory progTheory;
open pred_setTheory combinTheory;
open arm_decompTheory decompilerLib;

val ERR = Feedback.mk_HOL_ERR "arm_decompLib"

(* automation *)

local
   fun w_var i = Term.mk_var ("w" ^ Int.toString i, ``:word32``)
   fun word32 w = wordsSyntax.mk_wordi (Arbnum.fromHexString w, 32)
   val ok_rule = PURE_ONCE_REWRITE_RULE [GSYM arm_OK_def]
   val sbst =
      [``vfp:bool`` |-> boolSyntax.T, ``arch:Architecture`` |-> ``ARMv7_A``]
   fun arm_OK_intro l = ok_rule o Thm.INST (l @ sbst)
   fun format_thm th =
      (th, 4,
       stateLib.get_pc_delta
          (Lib.equal "arm_prog$arm_PC" o fst o boolSyntax.dest_strip_comb) th)
in
   val set_opt = arm_progLib.arm_config "vfp"
   fun l3_arm_triples hex =
      case String.tokens (fn c => c = #" ") hex of
         h :: r =>
           let
              val ws = List.tabulate (List.length r, w_var)
              val l =
                List.map (fn (v, hx) => v |-> word32 hx) (ListPair.zip (ws, r))
           in
              List.map (arm_OK_intro l)
                 (stateLib.fix_precond (arm_progLib.arm_spec_hex h))
           end
       | _ => raise ERR "l3_arm_triples" "empty string"
   fun l3_arm_spec hex =
      case List.map format_thm (l3_arm_triples hex) of
         [x] => (x, NONE)
       | [x1, x2] => (x1, SOME x2)
       | _ => raise ERR "l3_arm_spec" ""
   fun l3_arm_spec_opt s hex = (set_opt s; l3_arm_spec hex)
end

val arm_pc = Term.prim_mk_const {Thy = "arm_prog", Name = "arm_PC"}

fun arm_tools f hide = (f, fn _ => fail(), hide, arm_pc): decompiler_tools
fun arm_tools_opt opt = arm_tools (l3_arm_spec_opt opt)

val l3_arm_tools = arm_tools l3_arm_spec arm_progTheory.aS_HIDE
val l3_arm_tools_no_status = arm_tools l3_arm_spec TRUTH

val l3_arm_tools_array = arm_tools_opt "array" arm_progTheory.aS_HIDE
val l3_arm_tools_array_no_status = arm_tools_opt "array" TRUTH
val l3_arm_tools_mapped = arm_tools_opt "mapped" arm_progTheory.aS_HIDE
val l3_arm_tools_mapped_no_status = arm_tools_opt "mapped" TRUTH
val l3_arm_tools_mapped32 = arm_tools_opt "mapped32" arm_progTheory.aS_HIDE
val l3_arm_tools_mapped32_no_status = arm_tools_opt "mapped32" TRUTH

fun arm_decompile iscode tools opt name (qcode: string quotation) =
   let
      val q = if iscode then armAssemblerLib.arm_code
              else helperLib.quote_to_strings
      val decomp = decompilerLib.decompile_with q tools
   in
      set_opt opt
    ; arm_progLib.set_newline ""
    ; (decompilerLib.UNABBREV_CODE_RULE ## I) (decomp name qcode)
   end

val l3_arm_decompile = arm_decompile false l3_arm_tools "mapped"
val arm_decompile_code = arm_decompile true l3_arm_tools "mapped"

val l3_arm_decompile_no_status =
   arm_decompile false l3_arm_tools_no_status "mapped"

val arm_decompile_code_no_status =
   arm_decompile true l3_arm_tools_no_status "mapped"

val arm_decompile32 = arm_decompile false l3_arm_tools "mapped32"
val arm_decompile32_code = arm_decompile true l3_arm_tools "mapped32"

val arm_decompile32_no_status =
   arm_decompile false l3_arm_tools_no_status "mapped32"

val arm_decompile32_code_no_status =
   arm_decompile true l3_arm_tools_no_status "mapped32"

(* testing

open arm_decompLib

val q =
   `movs r1, #0        ; accumulator
    mov  r3, r0        ; first address
    adds r3, #40       ; last address (10 loads)
label:
    ldr  r2, [r0, #4]  ; load data
    adds r0, #4        ; increment address
    add  r1, r2        ; add to accumulator
    cmp  r0, r3        ; test if done
    blt  label         ; loop if not done`

val () = armAssemblerLib.print_arm_code q

val (test_cert, test_def) = arm_decompile_code "test" q

*)

end
