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

val l3_triple = helperLib.instruction_apply rule o spec

val vars = Term.mk_var ("cond", Type.bool) ::
           fst (boolSyntax.strip_forall (Thm.concl ARM_ASSERT_def))

val () = core_decompilerLib.configure
           { pc_tm = r15,
             init_fn = arm_decompLib.config_for_fast,
             pc_conv = RAND_CONV,
             triple_fn = l3_triple,
             component_vars = vars }

(* ------------------------------------------------------------------------ *)

end
