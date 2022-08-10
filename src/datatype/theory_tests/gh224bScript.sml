open HolKernel Parse boolLib

open gh224aTheory

val _ = new_theory "gh224b";

Theorem size_works:
  <| size := 3|>.size = 3
Proof
  simpLib.SIMP_TAC (BasicProvers.srw_ss()) []
QED


val _ = export_theory();
