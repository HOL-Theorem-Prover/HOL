open HolKernel boolLib bossLib
open arm_progLib

val () = new_theory "arm_saved_specs"

(* ------------------------------------------------------------------------ *)

val () = List.app arm_progLib.addInstructionClass
   ["ADD (imm)", "ADD (reg)",
    "SUB (imm)", "SUB (reg)",
    "TEQ (imm)", "TEQ (reg)",
    "TST (imm)", "TST (reg)",
    "B", "BEQ", "BNE", "BCS", "BCC",
    "LDR (+imm,pre)", "LDR (-imm,pre)",
    "STR (+imm,pre)", "STR (-imm,pre)"]

val saved_specs = arm_progLib.saveSpecs "saved_specs"

(* ------------------------------------------------------------------------ *)

val () = (Feedback.set_trace "TheoryPP.include_docs" 0; export_theory())
