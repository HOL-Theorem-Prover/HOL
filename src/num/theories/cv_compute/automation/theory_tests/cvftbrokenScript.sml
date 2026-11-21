Theory cvftbroken
Ancestors
  cvftbase
Libs
  cv_transLib

(* its own translation of colour, kept only under a premise that needs a
   translation of fnbox, which cannot be defined *)

Datatype:
  fnbox = FnBox (num -> num)
End

val _ = cv_typeLib.define_from_to “:colour”
val _ = cv_from_to_delete "cvftbroken.from_cvftbase_to_cvftbase_colour_thm"

Theorem broken_colour_thm[cv_from_to] =
  DISCH “from_to (f:fnbox -> cv) t”
    (theorem "from_cvftbase_to_cvftbase_colour_thm")
