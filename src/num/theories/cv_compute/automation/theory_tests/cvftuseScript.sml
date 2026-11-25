Theory cvftuse
Ancestors
  cvftleft cvftright
Libs
  cv_transLib

(* Both parents translate colour, and neither is an ancestor of the other.
   Loading them is fine, but a translation that needs colour fails until
   one of them is removed. *)

val _ = (cv_trans cvftbaseTheory.shade_def;
         raise Fail "used a clashing translation")
        handle HOL_ERR e =>
          if String.isSubstring "cv_from_to_delete" (Feedback.message_of e)
          then () else raise HOL_ERR e

val _ = cv_from_to_delete "cvftright.from_cvftbase_to_cvftbase_colour_thm"
val _ = cv_rep_delete "cvftright.cv_rep_cvftbase_cvftbase_colour_datatype"

val _ = cv_trans cvftbaseTheory.shade_def

Theorem shade_green = cv_eval “shade (Green 2)”

val _ = assert (aconv “3:num” o rhs o concl) shade_green
