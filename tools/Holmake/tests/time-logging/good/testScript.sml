open HolKernel Parse boolLib

val _ = new_theory "test";

val test = store_thm("test", “p ∧ p ⇔ p”, REWRITE_TAC[]);

val _ = export_theory();
