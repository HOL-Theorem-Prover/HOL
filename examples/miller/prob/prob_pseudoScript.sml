open HolKernel Parse boolLib bossLib;
open arithmeticTheory numTheory sequenceTheory
     sequenceTools hurdUtils combinTheory;

val _ = new_theory "prob_pseudo";

(* ------------------------------------------------------------------------- *)
(* The definition of the pseudo-random number generator.                     *)
(* ------------------------------------------------------------------------- *)

val prob_pseudo_def = Define
   `prob_pseudo a b n = siter EVEN (\x. (a * x + b) MOD (2 * n + 1))`;

(* ------------------------------------------------------------------------- *)
(* Theorems to allow pseudo-random bits to be computed.                      *)
(* ------------------------------------------------------------------------- *)

val SHD_PROB_PSEUDO = store_thm
  ("SHD_PROB_PSEUDO",
   ``!a b n x. shd (prob_pseudo a b n x) = EVEN x``,
   RW_TAC std_ss [prob_pseudo_def, SHD_SITER]);

val STL_PROB_PSEUDO = store_thm
  ("STL_PROB_PSEUDO",
   ``!a b n x.
       stl (prob_pseudo a b n x) =
       prob_pseudo a b n ((a * x + b) MOD (2 * n + 1))``,
   RW_TAC std_ss [prob_pseudo_def, STL_SITER]);

val _ = export_theory ();
