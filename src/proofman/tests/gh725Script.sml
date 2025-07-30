Theory gh725[bare]
Libs
  HolKernel Parse boolLib

val foo_def = new_definition ("foo_def", ``foo x <=> x /\ T``)
val bar_def = new_definition ("bar_def", ``bar (f:'b->'a) x = f x``)
Theorem th1 = TRUTH
Theorem th2 = CONJ TRUTH (REFL “x:'a”)

val _ = html_theory "gh725";
