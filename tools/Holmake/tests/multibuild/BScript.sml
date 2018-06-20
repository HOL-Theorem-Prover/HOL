open HolKernel Parse boolLib bossLib;

val _ = new_theory "B";

open multiLib

val _ = List.tabulate(10, genthms 0)


val _ = export_theory();
