(* ------------------------------------------------------------------------- *)
(* The monoids of addition and multiplication of real numbers.               *)
(* ------------------------------------------------------------------------- *)
(* The groups of addition and multiplication of real numbers.                *)
(* ------------------------------------------------------------------------- *)
(* Reals as a ring.                                                          *)
(* ------------------------------------------------------------------------- *)

open HolKernel boolLib bossLib Parse;

open pred_setTheory realTheory iterateTheory real_sigmaTheory dep_rewrite bagTheory
     monoidTheory groupTheory ringTheory;

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
  \\ simp[Reals_def, REAL_MUL_LINV, Invertibles_carrier]
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

Theorem Reals_sum_inv:
  Reals.sum.inv = real_neg
Proof
  rw[FUN_EQ_THM, Reals_def]
  \\ DEP_REWRITE_TAC[GSYM group_linv_unique]
  \\ simp[]
  \\ metis_tac[real_add_group, AbelianGroup_def]
QED

Theorem GBAG_Reals_sum_BAG_IMAGE_BAG_OF_SET:
  !f s. FINITE s ==>
  GBAG Reals.sum (BAG_IMAGE f (BAG_OF_SET s)) =
  REAL_SUM_IMAGE f s
Proof
  strip_tac
  \\ ho_match_mp_tac FINITE_INDUCT
  \\ rw[]
  >- rw[Reals_def, real_sigmaTheory.REAL_SUM_IMAGE_THM]
  \\ rw[real_sigmaTheory.REAL_SUM_IMAGE_THM]
  \\ fs[DELETE_NON_ELEMENT]
  \\ fs[GSYM DELETE_NON_ELEMENT]
  \\ rw[BAG_OF_SET_INSERT_NON_ELEMENT]
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ simp[]
  \\ simp[Reals_def]
QED

Theorem GBAG_Reals_prod_BAG_OF_SET:
  !f s. FINITE s ==>
  GBAG Reals.prod (BAG_IMAGE f (BAG_OF_SET s)) =
  product s f
Proof
  strip_tac
  \\ ho_match_mp_tac FINITE_INDUCT
  \\ rw[]
  >- rw[Reals_def, PRODUCT_CLAUSES]
  \\ rw[PRODUCT_CLAUSES]
  \\ fs[DELETE_NON_ELEMENT]
  \\ fs[GSYM DELETE_NON_ELEMENT]
  \\ rw[BAG_OF_SET_INSERT_NON_ELEMENT]
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ simp[]
  \\ simp[Reals_def]
QED

val _ = export_theory();
