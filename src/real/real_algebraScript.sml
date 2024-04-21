(* ------------------------------------------------------------------------- *)
(* The monoids of addition and multiplication of real numbers.               *)
(* ------------------------------------------------------------------------- *)

open HolKernel boolLib bossLib Parse;

open realTheory monoidTheory;

val _ = new_theory "real_algebra";

Definition real_add_monoid_def:
  real_add_monoid : real monoid =
  <| carrier := UNIV; id := 0; op := (real_add) |>
End

Theorem real_add_monoid_simps[simp]:
  real_add_monoid.carrier = UNIV /\
  real_add_monoid.op = (real_add) /\
  real_add_monoid.id = 0
Proof
  rw[real_add_monoid_def]
QED

Theorem real_add_monoid[simp]:
  AbelianMonoid real_add_monoid
Proof
  rw[AbelianMonoid_def]
  >- (
    rewrite_tac[Monoid_def]
    \\ simp[REAL_ADD_ASSOC] )
  \\ simp[REAL_ADD_COMM]
QED

Definition real_mul_monoid_def:
  real_mul_monoid : real monoid =
  <| carrier := UNIV; id := 1; op := (real_mul) |>
End

Theorem real_mul_monoid_simps[simp]:
  real_mul_monoid.carrier = UNIV /\
  real_mul_monoid.op = (real_mul) /\
  real_mul_monoid.id = 1
Proof
  rw[real_mul_monoid_def]
QED

Theorem real_mul_monoid[simp]:
  AbelianMonoid real_mul_monoid
Proof
  rw[AbelianMonoid_def]
  >- (
    rewrite_tac[Monoid_def]
    \\ simp[REAL_MUL_ASSOC] )
  \\ simp[REAL_MUL_COMM]
QED

val _ = export_theory();
