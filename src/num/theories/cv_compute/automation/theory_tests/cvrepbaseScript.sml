Theory cvrepbase
Ancestors[qualified]
  arithmetic
Libs
  cv_transLib

(* Shared ancestor for the cv_rep conflict tests: sq is translated here,
   dbl is translated by both cvrepclash1 and cvrepclash2, each in one
   theorem with a translation of inc1 or tpl respectively *)

Definition sq_def:
  sq n = n * n
End

val _ = cv_trans sq_def

Definition dbl_def:
  dbl n = n + n
End

Definition inc1_def:
  inc1 n = n + 1
End

Definition tpl_def:
  tpl n = 3 * n
End
