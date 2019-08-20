(*--------------------------------------------------------------------------
  Example 1
  -------------------------------------------------------------------------- *)

load "holyHammer"; open holyHammer;
open arithmeticTheory;
val cj = ``a <= b ==> (g ** (b - a) * g ** a = g ** b)``;
(* holyhammer cj; *)
val tactic = METIS_TAC [SUB_ADD, EXP_ADD];
val th = store_thm ("EXP_NEG", cj, tactic);
