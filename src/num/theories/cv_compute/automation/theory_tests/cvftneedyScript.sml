Theory cvftneedy
Ancestors
  cvftbase
Libs
  cv_transLib

(* its own translation of colour, kept only under a premise that needs a
   translation of tint, which has none yet *)

Datatype:
  tint = Tint num
End

val _ = cv_typeLib.define_from_to “:colour”
val _ = cv_from_to_delete "cvftneedy.from_cvftbase_to_cvftbase_colour_thm"

Theorem needy_colour_thm[cv_from_to] =
  DISCH “from_to (f:tint -> cv) t”
    (theorem "from_cvftbase_to_cvftbase_colour_thm")
