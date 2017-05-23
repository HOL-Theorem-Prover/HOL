open HolKernel Parse boolLib bossLib;

open proj1ATheory

val _ = new_theory "proj1B";

val Bthm = Q.store_thm(
  "Bthm",
  ‘SUC o foo = BIT2’,
  REWRITE_TAC[FUN_EQ_THM, combinTheory.o_THM, arithmeticTheory.BIT2] >>
  simp[foo_def]);

val _ = export_theory();
