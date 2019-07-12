open HolKernel Parse boolLib bossLib;

open comp_delbinding1Theory

val _ = new_theory "comp_delbinding2";

Theorem th = EVAL “foo 2”
val _ = rhs (concl th) ~~ lhs (concl th) orelse raise Fail "foo was evaluated!"

val _ = export_theory();
