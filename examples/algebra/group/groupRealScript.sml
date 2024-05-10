(* ------------------------------------------------------------------------- *)
(* The groups of addition and multiplication of real numbers.                *)
(* ------------------------------------------------------------------------- *)
open HolKernel boolLib bossLib Parse;

open pred_setTheory groupTheory monoidTheory real_algebraTheory;

val _ = new_theory"groupReal";

Theorem real_add_group[simp]:
  AbelianGroup real_add_monoid
Proof
  mp_tac real_add_monoid
  \\ rewrite_tac[AbelianMonoid_def]
  \\ rw[AbelianGroup_def, Group_def]
  \\ rw[monoid_invertibles_def]
  \\ simp[Once EXTENSION]
  \\ gen_tac \\ qexists_tac`-x`
  \\ simp[]
QED

Theorem real_mul_group:
  AbelianGroup (real_mul_monoid excluding 0)
Proof
  mp_tac real_mul_monoid
  \\ rewrite_tac[AbelianMonoid_def]
  \\ rw[AbelianGroup_def, Group_def]
  >- (
    full_simp_tac std_ss [Monoid_def]
    \\ fs[excluding_def] )
  \\ rw[monoid_invertibles_def]
  \\ simp[excluding_def, Once EXTENSION]
  \\ gen_tac \\ Cases_on`x = 0` \\ rw[]
  \\ qexists_tac`realinv x`
  \\ simp[realTheory.REAL_MUL_RINV]
QED

val _ = export_theory();
