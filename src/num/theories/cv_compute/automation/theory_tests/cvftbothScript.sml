Theory cvftboth
Ancestors
  cvftleft cvftright
Libs
  cv_transLib

(* A translation of colour added here takes precedence over those of
   cvftleft and cvftright, here and in cvftbothuse *)

val _ = cv_rep_delete "cvftleft.cv_rep_cvftbase_cvftbase_colour_datatype"
val _ = cv_rep_delete "cvftright.cv_rep_cvftbase_cvftbase_colour_datatype"

val _ = cv_typeLib.define_from_to “:colour”

val _ = assert (equal "cvftboth" o #Thy o dest_thy_const)
               (cv_typeLib.from_term_for “:colour”)
