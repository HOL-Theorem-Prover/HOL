open HolKernel Parse boolLib

val _ = new_theory "gh725";

val foo_def = new_definition ("foo_def", ``foo x <=> x /\ T``)
val bar_def = new_definition ("bar_def", ``bar (f:'b->'a) x = f x``)
Theorem th1 = TRUTH
Theorem th2 = CONJ TRUTH (REFL “x:'a”)

val _ = export_theory();
val _ = html_theory "gh725";
