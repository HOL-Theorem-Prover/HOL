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

(* one theorem translating dbl and tpl; only its dbl part clashes *)
val _ = cv_trans tpl_def
val _ = cv_rep_delete "cv_dbl_thm"
val _ = cv_rep_delete "cv_tpl_thm"

Theorem cv_dbl_tpl[cv_rep] =
  CONJ (theorem "cv_dbl_thm") (theorem "cv_tpl_thm")
