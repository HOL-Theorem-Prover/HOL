Theory gh725[bare]
Libs
  HolKernel Parse boolLib

Definition foo_def[nocompute]: foo x <=> x /\ T
End
Definition bar_def[nocompute]: bar (f:'b->'a) x = f x
End
Theorem th1 = TRUTH
Theorem th2 = CONJ TRUTH (REFL “x:'a”)

val _ = html_theory "gh725";
