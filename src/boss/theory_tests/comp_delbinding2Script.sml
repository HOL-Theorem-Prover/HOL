Theory comp_delbinding2
Ancestors
  comp_delbinding1

Theorem th = EVAL “foo 2”
val _ = rhs (concl th) ~~ lhs (concl th) orelse raise Fail "foo was evaluated!"

