Theory A
Libs
  foobarLib

Definition foo_def[foobar]:
  foo a = a + 1
End

Theorem foo_foo[foobar]:
  foo (foo a) = a + 2
Proof
  simp[foo_def]
QED

