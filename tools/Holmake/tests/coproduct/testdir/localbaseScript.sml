open HolKernel Parse boolLib

val _ = new_theory "localbase";

val lbT = save_thm("lbT", TRUTH);



val _ = export_theory();
