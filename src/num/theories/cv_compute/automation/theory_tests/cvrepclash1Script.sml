Theory cvrepclash1
Ancestors
  cvrepbase
Libs
  cv_transLib

val _ = cv_trans dbl_def

(* one theorem translating dbl and inc1; only its dbl part clashes *)
val _ = cv_trans inc1_def
val _ = cv_rep_delete "cv_dbl_thm"
val _ = cv_rep_delete "cv_inc1_thm"

Theorem cv_dbl_inc1[cv_rep] =
  CONJ (theorem "cv_dbl_thm") (theorem "cv_inc1_thm")
