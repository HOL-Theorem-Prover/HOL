Theory injected_strlit
Ancestors
  string

Datatype:  newtype = SINJ1 string | SINJ2 string | BORING num
End

val _ = add_strliteral_form {inj = “SINJ1”, ldelim = "«"}
val _ = add_strliteral_form {inj = “SINJ2”, ldelim = "‹"}


