open HolKernel Parse boolLib bossLib;

val _ = new_theory "proj1A";

val foo_def = Define`foo x = x * 2 + 1`;

val Athm = Q.store_thm(
  "Athm",
  `foo = BIT1`,
  REWRITE_TAC [FUN_EQ_THM, arithmeticTheory.BIT1] >>
  simp[foo_def]);



val _ = export_theory();
