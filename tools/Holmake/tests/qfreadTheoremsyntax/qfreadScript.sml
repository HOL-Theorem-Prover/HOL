open HolKernel Parse boolLib

val _ = new_theory "qfread";

Theorem foo = TRUTH;

Theorem bar = TRUTH;

val _ = export_theory();
