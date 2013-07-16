open HolKernel boolLib bossLib
open stateLib mips_stepTheory

infix \\
val op \\ = op THEN;

val () = new_theory "mips_prog"

(* ------------------------------------------------------------------------ *)

val _ =
   stateLib.sep_definitions "mips" [["CP0", "Status"], ["CP0", "Config"]] []
      mips_stepTheory.NextStateMIPS_def

val mips_instr_def = Define`
   mips_instr (a, i: word32) =
   { (mips_c_MEM a, mips_d_word8 ((7 >< 0) i));
     (mips_c_MEM (a + 1w), mips_d_word8 ((15 >< 8) i));
     (mips_c_MEM (a + 2w), mips_d_word8 ((23 >< 16) i));
     (mips_c_MEM (a + 3w), mips_d_word8 ((31 >< 24) i)) }`;

val MIPS_IMP_SPEC = Theory.save_thm ("MIPS_IMP_SPEC",
   Q.ISPECL [`mips_proj`, `NextStateMIPS`, `mips_instr`] stateTheory.IMP_SPEC
   )

(* ------------------------------------------------------------------------ *)

val () = export_theory()
