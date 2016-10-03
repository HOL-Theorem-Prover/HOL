open HolKernel Parse boolLib

val _ = new_theory "mergeGrammarsA2";

(* see comment at head of mergeGrammarsA1Script for description of what is
   being tested
*)

val a_theorem = store_thm(
  "a_theorem",
  ``(x:bool = x) /\ (y = y)``,
  REWRITE_TAC[]);


val _ = export_theory();
