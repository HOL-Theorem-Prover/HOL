Theory gh1413

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

val _ = assert (fn n => n = 1) (n2 - n1);

