open HolKernel Parse boolLib

open badLib

val _ = new_theory "A";

val A_def = new_definition ("A_def", ``A x = x``);

val A_thm = store_thm(
  "A_thm",
  ``p ==> (q ==> (r ==> A p))``,
  NTAC badLib.something STRIP_TAC >> ASM_REWRITE_TAC[A_def]);

val _ = export_theory();
