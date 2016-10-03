open HolKernel Parse boolLib

(* see comment at head of mergeGrammarsA1Script.sml for explanation of
   what is being tested here
*)

val _ = new_theory "mergeGrammarsB";

val my_theorem = save_thm(
  "my_theorem",
  CONJ mergeGrammarsA1Theory.a_theorem mergeGrammarsA2Theory.a_theorem);

val _ = export_theory();
