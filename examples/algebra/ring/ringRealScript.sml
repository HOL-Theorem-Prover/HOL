(* ------------------------------------------------------------------------- *)
(* Reals as a ring.                                                          *)
(* ------------------------------------------------------------------------- *)
open HolKernel boolLib bossLib Parse
     realTheory ringTheory ringMapTheory ringUnitTheory
     ringDividesTheory monoidRealTheory groupRealTheory

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

Theorem Unit_Reals[simp]:
  Unit Reals r <=> r <> 0
Proof
  simp[ring_unit_property]
  \\ simp[Reals_def]
  \\ rw[EQ_IMP_THM]
  >- (strip_tac \\ fs[])
  \\ qexists_tac`realinv r`
  \\ simp[REAL_MUL_RINV]
QED

Theorem Inv_Reals[simp]:
  r <> 0 ==> Inv Reals r = realinv r
Proof
  strip_tac
  \\ irule EQ_SYM
  \\ irule ring_unit_linv_unique
  \\ simp[]
  \\ simp[Reals_def, REAL_MUL_LINV, monoidOrderTheory.Invertibles_carrier]
QED

Theorem ring_divides_Reals:
  ring_divides Reals p q <=> (p = 0 ==> q = 0)
Proof
  rw[ring_divides_def]
  \\ rw[Reals_def]
  \\ Cases_on`p = 0` \\ simp[]
  \\ qexists_tac`q / p`
  \\ simp[REAL_DIV_RMUL]
QED

Theorem ring_prime_Reals[simp]:
  ring_prime Reals p
Proof
  rw[ring_prime_def]
  \\ fs[ring_divides_Reals]
  \\ fs[Reals_def]
QED

val _ = export_theory();
