Theory stagedTerminationAnc

(* Leaves suspended theorems with the names of stagedTermination's
   definitions, which must not be the ones that resuming and finalising
   those definitions reach, and of a plain theorem there *)

Theorem staged_def:
  p ==> p
Proof
  suspend "tc"
QED

Theorem prepared_def:
  p /\ q ==> p
Proof
  suspend "tc"
QED

Theorem shadowed:
  p \/ q ==> q \/ p
Proof
  suspend "sh"
QED
