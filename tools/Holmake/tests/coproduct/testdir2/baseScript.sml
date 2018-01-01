open HolKernel Parse boolLib

val _ = new_theory "base";

val Q_implies_Q = store_thm(
  "Q_implies_Q",
  ``Q ==> Q``,
  STRIP_TAC);

val _ = export_theory();
