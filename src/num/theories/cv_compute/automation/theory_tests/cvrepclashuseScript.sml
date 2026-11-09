Theory cvrepclashuse
Ancestors
  cvrepclash1 cvrepclash2
Libs
  cv_transLib

(* Both parents translate dbl differently.  Loading them is fine, but a
   translation that needs dbl fails until one of them is removed. *)

Definition quad_def:
  quad n = dbl (dbl n)
End

val _ = (cv_trans quad_def; raise Fail "used an ambiguous translation")
        handle HOL_ERR e =>
          if String.isSubstring "ambiguous" (Feedback.message_of e) then ()
          else raise HOL_ERR e

val _ = cv_rep_delete "cvrepclash2.cv_dbl_thm"

val _ = cv_trans quad_def

Theorem quad_3 = cv_eval “quad 3”

val _ = assert (aconv “12:num” o rhs o concl) quad_3
