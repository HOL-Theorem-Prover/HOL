Theory cvftboth
Ancestors
  cvftleft cvftright
Libs
  cv_transLib

(* A translation of colour added here does not settle the clash between
   cvftleft's and cvftright's; removing one of theirs does, and then the
   one added here is used *)

val _ = cv_rep_delete "cvftleft.cv_rep_cvftbase_cvftbase_colour_datatype"
val _ = cv_rep_delete "cvftright.cv_rep_cvftbase_cvftbase_colour_datatype"

val _ = cv_typeLib.define_from_to “:colour”

fun from_thy ty =
  cv_typeLib.from_term_for ty |> dest_thy_const |> #Thy

val _ = assert (fn ty => (from_thy ty; false) handle HOL_ERR e =>
                  String.isSubstring "cv_from_to_delete"
                                     (Feedback.message_of e))
               “:colour”

val _ = cv_from_to_delete "cvftleft.from_cvftbase_to_cvftbase_colour_thm"

val _ = assert (equal "cvftboth" o from_thy) “:colour”
