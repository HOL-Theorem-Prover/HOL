Theory localthA

Definition foo[simp]: foo = 3
End

Definition bar: bar = 3
End

Theorem bar_thm[simp,local]:
  bar = 3
Proof
  simp[bar]
QED

Theorem foo_bar:
  foo = bar
Proof
  simp[]
QED

