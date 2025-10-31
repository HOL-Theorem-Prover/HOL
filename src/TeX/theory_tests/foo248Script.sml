Theory foo248

Definition foo_def:
  foo a b = (a < b)
End
Overload "<:" = ``\a b. foo b a``
