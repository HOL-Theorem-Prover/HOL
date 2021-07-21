(* ------------------------------------------------------------------------- *)
(* Reals as a ring.                                                          *)
(* ------------------------------------------------------------------------- *)
open HolKernel boolLib bossLib Parse
     realTheory ringTheory monoidRealTheory groupRealTheory

val _ = new_theory"ringReal";

Definition Reals_def:
  Reals =
    <| carrier := UNIV;
       sum := real_add_monoid;
       prod := real_mul_monoid
    |>
End

Theorem RingReals[simp]:
  Ring Reals
Proof
  rewrite_tac[Ring_def]
  \\ simp[Reals_def, REAL_LDISTRIB]
QED

val _ = export_theory();
