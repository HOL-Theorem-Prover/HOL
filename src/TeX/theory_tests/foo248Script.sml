Theory foo248

Definition foo_def:
  foo a b = (a < b)
End
val _ = overload_on("<:",``\a b. foo b a``);
