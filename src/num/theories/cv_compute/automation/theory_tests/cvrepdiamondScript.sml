Theory cvrepdiamond
Ancestors
  cvrepleft cvrepright
Libs
  cv_transLib

(* sq's translation reaches this theory through both parents; that is
   not a conflict *)

Definition both_sq_def:
  both_sq n = left_sq n + right_sq n + sq n
End

val _ = cv_trans both_sq_def

Theorem both_sq_3 = cv_eval “both_sq 3”
