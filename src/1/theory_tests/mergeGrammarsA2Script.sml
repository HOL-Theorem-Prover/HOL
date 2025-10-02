Theory mergeGrammarsA2[bare]
Libs
  HolKernel Parse boolLib

(* see comment at head of mergeGrammarsA1Script for description of what is
   being tested
*)

Theorem a_theorem:
    (x:bool = x) /\ (y = y)
Proof
  REWRITE_TAC[]
QED


