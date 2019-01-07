open HolKernel Parse boolLib

open proj1BTheory
val _ = new_theory "proj2A";

val bar_def = new_definition ("bar_def", “bar x y <=> x /\ y”);

val thm2A = store_thm(
  "thm2A",
  “!y. bar F y <=> ~foo y”,
  REWRITE_TAC[bar_def, proj1ATheory.foo_def]);

val _ = export_theory();
