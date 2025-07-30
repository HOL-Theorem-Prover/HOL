Theory someplaceguy
Ancestors[qualified]
  arithmetic
Libs
  cv_transLib

Definition square_def:
  square n = n * n
End
val _ = cv_trans square_def


Theorem sq1234567 = time cv_eval “square 1234567”
Theorem sq1234567' = time EVAL “square 1234567”

val t1524155677489 =
  assert (aconv (rhs (concl sq1234567))) (rhs (concl sq1234567'))

