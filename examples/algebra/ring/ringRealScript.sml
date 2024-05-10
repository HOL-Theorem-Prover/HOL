(* ------------------------------------------------------------------------- *)
(* Reals as a ring.                                                          *)
(* ------------------------------------------------------------------------- *)
open HolKernel boolLib bossLib Parse;

open dep_rewrite realTheory pred_setTheory bagTheory real_sigmaTheory
     iterateTheory monoidTheory real_algebraTheory;

open ringTheory ringMapTheory ringUnitTheory ringDividesTheory groupRealTheory;

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
  \\ DEP_REWRITE_TAC[GSYM groupTheory.group_linv_unique]
  \\ simp[]
  \\ metis_tac[groupRealTheory.real_add_group, groupTheory.AbelianGroup_def]
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
  >- rw[Reals_def, iterateTheory.PRODUCT_CLAUSES]
  \\ rw[iterateTheory.PRODUCT_CLAUSES]
  \\ fs[DELETE_NON_ELEMENT]
  \\ fs[GSYM DELETE_NON_ELEMENT]
  \\ rw[BAG_OF_SET_INSERT_NON_ELEMENT]
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ simp[]
  \\ simp[Reals_def]
QED

val _ = export_theory();
