open HolKernel Parse boolLib bossLib;

open emitrecordTheory emitRecordTestML

val _ = new_theory "useEmitRecord";

val _ = save_thm("T", TRUTH)


val _ = export_theory();
