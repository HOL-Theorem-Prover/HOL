Theory prob_pseudo
Ancestors
  arithmetic num sequence combin
Libs
  sequenceTools hurdUtils

(* ------------------------------------------------------------------------- *)
(* The definition of the pseudo-random number generator.                     *)
(* ------------------------------------------------------------------------- *)

Definition prob_pseudo_def:
    prob_pseudo a b n = siter EVEN (\x. (a * x + b) MOD (2 * n + 1))
End

(* ------------------------------------------------------------------------- *)
(* Theorems to allow pseudo-random bits to be computed.                      *)
(* ------------------------------------------------------------------------- *)

Theorem SHD_PROB_PSEUDO:
     !a b n x. shd (prob_pseudo a b n x) = EVEN x
Proof
   RW_TAC std_ss [prob_pseudo_def, SHD_SITER]
QED

Theorem STL_PROB_PSEUDO:
     !a b n x.
       stl (prob_pseudo a b n x) =
       prob_pseudo a b n ((a * x + b) MOD (2 * n + 1))
Proof
   RW_TAC std_ss [prob_pseudo_def, STL_SITER]
QED

