Theory cvrepbase
Ancestors[qualified]
  arithmetic
Libs
  cv_transLib

(* Shared ancestor for the cv_rep conflict tests: sq is translated here,
   dbl is translated by both cvrepclash1 and cvrepclash2 *)

Definition sq_def:
  sq n = n * n
End

val _ = cv_trans sq_def

Definition dbl_def:
  dbl n = n + n
End
