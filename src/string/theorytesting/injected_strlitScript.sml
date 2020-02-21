open HolKernel Parse boolLib bossLib;

open stringTheory

val _ = new_theory "injected_strlit";

Datatype:  newtype = SINJ1 string | SINJ2 string | BORING num
End

val _ = add_strliteral_form {inj = “SINJ1”, ldelim = "«"}              (* UOK *)
val _ = add_strliteral_form {inj = “SINJ2”, ldelim = "‹"}              (* UOK *)


val _ = export_theory();
