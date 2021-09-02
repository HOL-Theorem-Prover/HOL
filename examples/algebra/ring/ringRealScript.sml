(* ------------------------------------------------------------------------- *)
(* Reals as a ring.                                                          *)
(* ------------------------------------------------------------------------- *)
open HolKernel boolLib bossLib Parse
     realTheory ringTheory ringMapTheory ringUnitTheory
     monoidRealTheory groupRealTheory

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

val _ = export_theory();
