open HolKernel Parse boolLib bossLib;

open cv_transLib

val _ = new_theory "someplaceguy";

val _ = set_grammar_ancestry ["arithmetic"]

Definition square_def:
  square n = n * n
End
val _ = cv_trans square_def


Theorem sq1234567 = time cv_eval “square 1234567”
Theorem sq1234567' = time EVAL “square 1234567”

val t1524155677489 =
  assert (aconv (rhs (concl sq1234567))) (rhs (concl sq1234567'))

val _ = export_theory();
