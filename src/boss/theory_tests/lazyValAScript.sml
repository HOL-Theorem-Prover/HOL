Theory lazyValA

Datatype:
  lazyty = LazyC1 | LazyC2 num
End

Definition lazyf_def:
  lazyf LazyC1 = 0 /\ lazyf (LazyC2 n) = n + 1
End

Theorem lazyf_two[simp]:
  lazyf (LazyC2 2) = 3
Proof
  simp[lazyf_def]
QED

Overload lazyo = “LazyC2 5”
