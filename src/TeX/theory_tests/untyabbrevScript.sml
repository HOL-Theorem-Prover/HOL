open HolKernel Parse boolLib bossLib;

open tyabbrevTheory

val _ = new_theory "untyabbrev";

val _ = Parse.disable_tyabbrev_printing "reln"


val _ = export_theory();
