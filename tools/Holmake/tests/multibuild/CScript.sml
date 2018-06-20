open HolKernel Parse boolLib bossLib;

val _ = new_theory "C";
open multiLib BTheory

val _ = List.tabulate(10, genthms 500)



val _ = export_theory();
