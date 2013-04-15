open HolKernel boolLib bossLib
open stateLib arm_stepTheory

infix \\
val op \\ = op THEN;

val () = new_theory "arm_prog"

(* ------------------------------------------------------------------------ *)

val _ =
   stateLib.sep_definitions "arm" [["CPSR"], ["FP", "FPSCR"]]
      arm_stepTheory.NextStateARM_def

val arm_instr_def = Define`
   arm_instr (a, i: word32) =
   { (arm_c_MEM a, arm_d_word8 ((7 >< 0) i));
     (arm_c_MEM (a + 1w), arm_d_word8 ((15 >< 8) i));
     (arm_c_MEM (a + 2w), arm_d_word8 ((23 >< 16) i));
     (arm_c_MEM (a + 3w), arm_d_word8 ((31 >< 24) i)) }`;

val ARM_IMP_SPEC = Theory.save_thm ("ARM_IMP_SPEC",
   Q.ISPECL [`arm_proj`, `NextStateARM`, `arm_instr`] stateTheory.IMP_SPEC
   )

(* ------------------------------------------------------------------------ *)

val () = export_theory()
