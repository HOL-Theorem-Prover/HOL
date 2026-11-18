Theory stagedTerminationAnc

(* Leaves a suspended theorem with the name of stagedTermination's
   definition, which must not be the one that resuming and finalising
   that definition reach *)

Theorem staged_def:
  p ==> p
Proof
  suspend "tc"
QED
