Theory gh1612A
Ancestors hol

Inductive even:
[~zero:] even 0
[~plus2:] even n ⇒ even (n + 2)
End

Definition foo_def:
  foo x = (x + 2) * 10
End
