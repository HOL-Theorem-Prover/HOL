open HolKernel boolLib bossLib

val () = new_theory "bug";

Definition apply_def:
  apply f x = f x
End

val n1 = List.length $ DefnBase.read_congs();

Theorem apply_cong[defncong]:
  (!x. f x = f' x)
  ==>
  apply f = apply f'
Proof
  rw[apply_def, FUN_EQ_THM]
QED

val n2 = List.length $ DefnBase.read_congs();

val 1 = n2 - n1;

val () = export_theory();
