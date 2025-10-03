Theory mergeGrammarsB[bare]
Libs
  HolKernel Parse boolLib

(* see comment at head of mergeGrammarsA1Script.sml for explanation of
   what is being tested here
*)

Theorem my_theorem =
  CONJ mergeGrammarsA1Theory.a_theorem mergeGrammarsA2Theory.a_theorem;

