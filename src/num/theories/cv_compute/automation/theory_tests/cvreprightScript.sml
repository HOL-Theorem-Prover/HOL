Theory cvrepright
Ancestors
  cvrepbase
Libs
  cv_transLib

Definition right_sq_def:
  right_sq n = sq n + 1
End

val _ = cv_trans right_sq_def
