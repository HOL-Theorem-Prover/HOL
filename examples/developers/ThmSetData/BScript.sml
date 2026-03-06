Theory B
Libs
  foobarLib

Definition bar_def[foobar]:
  bar a = a - 1
End

Theorem bar_bar[foobar]:
  bar (bar a) = a - 2
Proof
  simp[bar_def]
QED

