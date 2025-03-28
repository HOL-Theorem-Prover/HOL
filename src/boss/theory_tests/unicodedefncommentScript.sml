open HolKernel Parse boolLib bossLib;

val _ = new_theory "unicodedefncomment";

Datatype:
  foo = Con1 num (* x ≤ y *) | Con2 foo
End

Definition baz_def:
  baz (Con1 n (* x ≤ y *)) = n + 1 ∧
  baz (Con2 f) = 1 + baz f
End



val _ = export_theory();
