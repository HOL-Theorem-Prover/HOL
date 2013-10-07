open HolKernel Parse boolLib bossLib
open arm_progTheory

val () = new_theory "arm_decomp"

val arm_OK_def = Define `arm_OK mode = arm_CONFIG (T, ARMv7_A, F, F, mode)`

val () = export_theory()
