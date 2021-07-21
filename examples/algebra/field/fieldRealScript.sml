(* ------------------------------------------------------------------------- *)
(* The field of reals.                                                       *)
(* ------------------------------------------------------------------------- *)
open HolKernel boolLib bossLib Parse
     groupTheory fieldTheory ringRealTheory groupRealTheory

val _ = new_theory"fieldReal";

Theorem FieldReals[simp]:
  Field Reals
Proof
  rewrite_tac[Field_def]
  \\ conj_tac >- simp[]
  \\ simp[Reals_def]
  \\ metis_tac[real_mul_group, AbelianGroup_def]
QED

val _ = export_theory();
