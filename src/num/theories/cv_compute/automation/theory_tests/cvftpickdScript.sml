Theory cvftpickd
Ancestors
  cvftpickright
Libs
  cv_transLib

(* a descendant of cvftpickright, but not of cvftrightdup, with its own
   translation of colour *)

val _ = cv_rep_delete "cvftleft.cv_rep_cvftbase_cvftbase_colour_datatype"
val _ = cv_rep_delete "cvftright.cv_rep_cvftbase_cvftbase_colour_datatype"

val _ = cv_typeLib.define_from_to “:colour”
