open HolKernel Parse boolLib

open proj1ATheory

val _ = new_theory "proj1B";

val Bthm = store_thm(
  "Bthm",
  “(\f g x. f (g x)) (~) foo = \x. F”,
  BETA_TAC >> REWRITE_TAC[FUN_EQ_THM, foo_def]);

val _ = export_theory();
