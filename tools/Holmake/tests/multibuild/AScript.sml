open HolKernel Parse boolLib bossLib;


open multiLib
val _ = new_theory "A";

val _ = List.tabulate(10, genthms 1000)


val _ = export_theory();
