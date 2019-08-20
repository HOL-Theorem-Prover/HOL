open HolKernel Parse boolLib

open ATheory

val _ = new_theory "B";

val B = store_thm(
  "B",
  ``A p /\ q ==> p /\ q``,
  REWRITE_TAC[] THEN
  CONV_TAC (LAND_CONV (LAND_CONV (REWRITE_CONV [A_def]))) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);

val _ = export_theory();
