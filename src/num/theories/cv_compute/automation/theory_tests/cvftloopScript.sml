Theory cvftloop
Ancestors
  cvftbase
Libs
  cv_transLib

(* its own translation of colour, kept only under a premise that needs a
   translation of colour *)

val _ = cv_typeLib.define_from_to “:colour”
val _ = cv_from_to_delete "cvftloop.from_cvftbase_to_cvftbase_colour_thm"

Theorem loop_colour_thm[cv_from_to] =
  DISCH “from_to (f:colour -> cv) t”
    (theorem "from_cvftbase_to_cvftbase_colour_thm")
