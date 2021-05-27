open HolKernel Parse boolLib bossLib;
open foobarLib;

val _ = new_theory "B";

Definition bar_def[foobar]:
  bar a = a - 1
End

Theorem bar_bar[foobar]:
  bar (bar a) = a - 2
Proof
  simp[bar_def]
QED

val _ = export_theory ()
