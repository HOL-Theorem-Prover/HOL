Theory cvrepclash2
Ancestors
  cvrepbase
Libs
  cv_transLib

Theorem dbl_mult:
  dbl n = 2 * n
Proof
  simp[dbl_def]
QED

val _ = cv_trans dbl_mult
