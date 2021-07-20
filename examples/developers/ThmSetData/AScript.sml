open HolKernel Parse boolLib bossLib;
open foobarLib;

val _ = new_theory "A";

Definition foo_def[foobar]:
  foo a = a + 1
End

Theorem foo_foo[foobar]:
  foo (foo a) = a + 2
Proof
  simp[foo_def]
QED

val _ = export_theory ()
