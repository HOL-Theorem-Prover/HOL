structure arm_core_decompLib :> arm_core_decompLib =
struct

open HolKernel Parse boolLib bossLib Lib
open core_decompilerLib
open tripleLib arm_decompLib arm_core_decompTheory

val ERR = Feedback.mk_HOL_ERR "arm_core_decompLib"

(* ------------------------------------------------------------------------ *)

val (spec, _, _, _) = arm_decompLib.l3_arm_tools

val r15 = Term.mk_var ("r15", ``:word32``)

val rule = tripleLib.spec_to_triple_rule (r15, ARM_ASSERT_def, L3_ARM_def)

val l3_triple =
   (* utilsLib.cache 10000 String.compare *)
      (helperLib.instruction_apply rule o spec)

val l3_triple_code =
   List.map l3_triple o
   (armAssemblerLib.arm_code: string quotation -> string list)

val vars = Term.mk_var ("cond", Type.bool) ::
           fst (boolSyntax.strip_forall (Thm.concl ARM_ASSERT_def))

fun config_for_arm () =
   core_decompilerLib.configure
     { pc_tm = r15,
       init_fn = fn () => arm_progLib.arm_config "vfp"
                            "fpr-map, no-gpr-map, mapped",
       pc_conv = RAND_CONV,
       triple_fn = l3_triple,
       component_vars = vars }

val () = config_for_arm ()

fun arm_core_decompile name qcode =
   ( config_for_arm ()
   ; core_decompilerLib.code_parser := NONE
   ; core_decompilerLib.core_decompile name qcode
   )

fun arm_core_decompile_code name qcode =
   ( config_for_arm ()
   ; core_decompilerLib.code_parser := SOME armAssemblerLib.arm_code
   ; core_decompilerLib.core_decompile name qcode
   )

(* ------------------------------------------------------------------------ *)

end
