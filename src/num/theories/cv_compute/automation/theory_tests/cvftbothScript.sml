Theory cvftboth
Ancestors
  cvftleft cvftright
Libs
  cv_transLib

(* A translation of colour added here does not settle the clash between
   cvftleft's and cvftright's; removing one of theirs does, and then the
   one added here is used, here and in cvftbothuse *)

val _ = cv_rep_delete "cvftleft.cv_rep_cvftbase_cvftbase_colour_datatype"
val _ = cv_rep_delete "cvftright.cv_rep_cvftbase_cvftbase_colour_datatype"

val _ = cv_typeLib.define_from_to “:colour”

fun fails_with_clash ty =
  (cv_typeLib.from_term_for ty; false)
  handle HOL_ERR e =>
    String.isSubstring "cv_from_to_delete" (Feedback.message_of e)

val _ = assert fails_with_clash “:colour”

val _ = cv_from_to_delete "cvftleft.from_cvftbase_to_cvftbase_colour_thm"

val _ = assert (equal "cvftboth" o #Thy o dest_thy_const)
               (cv_typeLib.from_term_for “:colour”)
