open HolKernel Parse boolLib bossLib
open arm_progTheory

val _ = new_theory "arm_decomp"

val arm_OK_def = Define `arm_OK mode = arm_CONFIG (T, ARMv7_A, F, mode)`

val _ = export_theory()
