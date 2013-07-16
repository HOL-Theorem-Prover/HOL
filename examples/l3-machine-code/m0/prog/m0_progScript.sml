open HolKernel boolLib bossLib
open stateLib m0_stepTheory

val () = new_theory "m0_prog"

(* ------------------------------------------------------------------------ *)

val _ = stateLib.sep_definitions "m0" [["PSR"], ["CONTROL"]] [["pcinc"]]
           m0_stepTheory.NextStateARM_def

val m0_instr_def = Define`
  (m0_instr (a, INL (opc16: word16)) =
   { (m0_c_MEM a, m0_d_word8 ((7 >< 0) opc16));
     (m0_c_MEM (a + 1w), m0_d_word8 ((15 >< 8) opc16)) }) /\
  (m0_instr (a, INR (opc32: word32)) =
   { (m0_c_MEM a, m0_d_word8 ((23 >< 16) opc32));
     (m0_c_MEM (a + 1w), m0_d_word8 ((31 >< 24) opc32));
     (m0_c_MEM (a + 2w), m0_d_word8 ((7 >< 0) opc32));
     (m0_c_MEM (a + 3w), m0_d_word8 ((15 >< 8) opc32)) })`;

val M0_IMP_SPEC = Theory.save_thm ("M0_IMP_SPEC",
   Q.ISPECL [`m0_proj`, `NextStateARM`, `m0_instr`] stateTheory.IMP_SPEC
   )

(* ------------------------------------------------------------------------ *)

val () = export_theory()
