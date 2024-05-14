(* ------------------------------------------------------------------------- *)
(* The field of reals.                                                       *)
(* ------------------------------------------------------------------------- *)

open HolKernel boolLib bossLib Parse;

open groupTheory fieldTheory real_algebraTheory;

val _ = new_theory "fieldReal";

Theorem FieldReals[simp]:
  Field Reals
Proof
  rewrite_tac[Field_def]
  \\ conj_tac >- simp[]
  \\ simp[Reals_def]
  \\ metis_tac[real_mul_group, AbelianGroup_def]
QED

Theorem IntegralDomainReals[simp]:
  IntegralDomain Reals
Proof
  metis_tac[field_is_integral_domain, FieldReals]
QED

val _ = export_theory();
