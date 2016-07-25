open HolKernel Parse boolLib

val _ = new_theory "usedCheat";

val x = prove(``p /\ q ==> r``, ALL_TAC);

val th = save_thm("th", TRUTH);


val _ = export_theory();
