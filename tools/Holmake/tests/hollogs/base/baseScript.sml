open HolKernel Parse boolLib

val _ = new_theory "base";

val base = store_thm("base", ``x:'a = x``, REWRITE_TAC[]);


val _ = export_theory();
