Theory cvftpickright
Ancestors
  cvftleft cvftright
Libs
  cv_memLib

(* a descendant of both keeps cvftright's translation of colour, by
   removing cvftleft's, and registers it again under another name *)

val _ = cv_memLib.cv_from_to_delete
          "cvftleft.from_cvftbase_to_cvftbase_colour_thm"

Theorem pick_colour_thm[cv_from_to] =
  cvftrightTheory.from_cvftbase_to_cvftbase_colour_thm
