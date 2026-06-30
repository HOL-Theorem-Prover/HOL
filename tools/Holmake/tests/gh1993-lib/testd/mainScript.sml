open HolKernel Parse boolLib badLib;

val _ = new_theory "main";

Theorem trivial:
  T
Proof
  ACCEPT_TAC TRUTH
QED

val _ = export_theory();
