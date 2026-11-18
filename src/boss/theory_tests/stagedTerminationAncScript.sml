Theory stagedTerminationAnc

(* Leaves suspended theorems with the names of stagedTermination's
   definitions, which must not be the ones that resuming and finalising
   those definitions reach *)

Theorem staged_def:
  p ==> p
Proof
  suspend "tc"
QED

Theorem prepared_def:
  p ==> p
Proof
  suspend "tc"
QED
