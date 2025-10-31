Theory theory1

val _ = set_trace "Theory.allow_rebinds" 1

val _ = register_hook("magnus_bug",
                      (fn TheoryDelta.ExportTheory _ => delete_const "h"
                        | _ => ()))

Definition f_def:  f x = x + 1
End
val _ = export_rewrites ["f_def"]

Definition g_def:  g n m = f (n * m)
End
val _ = export_rewrites ["g_def"]

val i = EVAL ``g 3 4``
             |> concl |> rhs |> numSyntax.dest_numeral
             |> Arbnum.toInt
             |> assert (equal 13)

val _ = delete_const "g";

Definition h_def:
  h n = n + 1
End

Definition f2_def:  f2 n = n + 1
End
val _ = export_rewrites ["f2_def"]

Theorem f2_SUC:
    f2 = SUC
Proof
  REWRITE_TAC [arithmeticTheory.ADD1, f2_def, FUN_EQ_THM]
QED

val _ = delete_binding "f2_def"

Definition f3_def:  f3 n = n + 1
End
Definition f3_def:  f3 n = n + 2
End
Definition f3_def:  f3 n = n + 3
End
Definition f3_def:  f3 n = n + 4
End

Definition g3_def:  g3 n = f3 (n + 1)
End
Definition f3_def:  f3 n = n + 5
End


