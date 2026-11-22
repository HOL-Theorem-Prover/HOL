Theory cvftfaild
Ancestors
  cvftleft cvftright
Libs
  cv_memLib

(* a descendant of both with a translation of colour that does not apply
   to it: its premise needs a translation of a function type *)

Theorem faild_colour_thm[cv_from_to] =
  DISCH “from_to (f:(num -> num) -> cv) t”
    cvftrightTheory.from_cvftbase_to_cvftbase_colour_thm
