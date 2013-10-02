open HolKernel Parse boolLib bossLib;
open m0_progTheory

val _ = new_theory "m0_decomp";

val m0_COUNT_def = Define `m0_COUNT count = m0_count count * m0_CONFIG (F, F)`

val _ = export_theory()
