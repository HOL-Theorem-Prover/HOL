structure arm_decompLib :> arm_decompLib =
struct

open HolKernel Parse boolLib bossLib;
open helperLib set_sepTheory addressTheory progTheory;
open pred_setTheory combinTheory;
open arm_decompTheory decompilerLib;

val ERR = Feedback.mk_HOL_ERR "arm_decompLib"

local
   datatype configuration = Uninitialised | Original | Fast
   val config = ref Uninitialised
in
   fun config_for_original () =
      case !config of
         Original => ()
       | _ => (arm_progLib.arm_config "vfp, no-fpr-map, no-gpr-map, mem-map"
               ; arm_progLib.set_newline ""
               ; config := Original)
   fun config_for_fast () =
      case !config of
         Fast => ()
       | _ => (arm_progLib.arm_config "vfp, fpr-map, no-gpr-map, mem-map"
               ; arm_progLib.set_newline ""
               ; config := Fast)
end

(* automation *)

local
   val w0_var = mk_var ("w0", ``:word32``)
   val ok_rule = PURE_ONCE_REWRITE_RULE [GSYM arm_OK_def]
   val sbst =
      [``vfp:bool`` |-> boolSyntax.T, ``arch:Architecture`` |-> ``ARMv7_A``]
   fun arm_OK_intro w0 = ok_rule o Thm.INST ((w0_var |-> w0) :: sbst)
   fun format_thm th =
      (th, 4,
       stateLib.get_pc_delta
          (Lib.equal "arm_prog$arm_PC" o fst o boolSyntax.dest_strip_comb) th)
in
   fun l3_arm_triples hex =
      let
         val hs = String.tokens (fn c => c = #" ") hex
         val xs = stateLib.fix_precond (arm_progLib.arm_spec_hex (hd hs))
         val w0 = wordsSyntax.mk_wordi (Arbnum.fromHexString (last hs), 32)
     in
        List.map (arm_OK_intro w0) xs
     end
   fun l3_arm_spec hex =
      case List.map format_thm (l3_arm_triples hex) of
         [x] => (x, NONE)
       | [x1, x2] => (x1, SOME x2)
       | _ => raise ERR "l3_arm_spec" ""
end

val (l3_arm_tools: decompiler_tools) =
   (l3_arm_spec, fn _ => fail(), arm_progTheory.aS_HIDE, ``arm_PC``)

val (l3_arm_tools_no_status: decompiler_tools) =
   (l3_arm_spec, fn _ => fail(), TRUTH, ``arm_PC``)

fun l3_arm_decompile name qcode =
   let
      val () = config_for_original ()
      val (result, func) = decompile l3_arm_tools name qcode
      val result = UNABBREV_CODE_RULE result
   in
      (result,func)
   end

fun l3_arm_decompile_no_status name qcode =
   let
      val () = config_for_original ()
      val (result, func) = decompile l3_arm_tools_no_status name qcode
      val result = UNABBREV_CODE_RULE result
   in
      (result,func)
   end

(* testing

open rel_decompilerLib

val hex = "B0821003"
val hex = "07921003"

val l3_arm_spec = Count.apply l3_arm_spec

  l3_arm_spec "07921003";
  l3_arm_spec "17921003";
  l3_arm_spec "27921003";
  l3_arm_spec "37921003";
  l3_arm_spec "47921003";
  l3_arm_spec "57921003";
  l3_arm_spec "67921003";
  l3_arm_spec "77921003";
  l3_arm_spec "87921003";
  l3_arm_spec "97921003";
  l3_arm_spec "A7921003";
  l3_arm_spec "B7921003";
  l3_arm_spec "C7921003";
  l3_arm_spec "D7921003";
  l3_arm_spec "E7921003";

fast_decompile "test" `e59f322c  00012f94`

*)

end
