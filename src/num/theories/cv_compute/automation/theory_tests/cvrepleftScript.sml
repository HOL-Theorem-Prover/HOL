Theory cvrepleft
Ancestors
  cvrepbase
Libs
  cv_transLib

Definition left_sq_def:
  left_sq n = sq n + 1
End

val _ = cv_trans left_sq_def
