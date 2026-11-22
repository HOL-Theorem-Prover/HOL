Theory cvftrightdup2
Ancestors
  cvftright
Libs
  cv_memLib

(* registers cvftright's translation of colour again, as the unrelated
   cvftrightdup does *)

Theorem dup2_colour_thm[cv_from_to] =
  cvftrightTheory.from_cvftbase_to_cvftbase_colour_thm
