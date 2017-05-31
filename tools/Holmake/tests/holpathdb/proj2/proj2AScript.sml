open HolKernel Parse boolLib bossLib;

open proj1BTheory
val _ = new_theory "proj2A";

val bar_def = Define‘bar x = 2 * x - 1’;

val thm2A = Q.store_thm(
  "thm2A",
  ‘∀n. 0 < n ⇒ (bar n = foo n - 2)’,
  simp[bar_def, proj1ATheory.foo_def]);

val _ = export_theory();
