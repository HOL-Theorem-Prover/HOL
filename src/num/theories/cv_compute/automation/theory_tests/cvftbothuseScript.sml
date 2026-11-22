Theory cvftbothuse
Ancestors
  cvftboth
Libs
  cv_transLib

(* cvftboth removed cvftleft's translation of colour, and cvftright is
   its ancestor, so its translation is used without a clash *)

val _ = assert (equal "cvftboth" o #Thy o dest_thy_const)
               (cv_typeLib.from_term_for “:colour”)

val _ = cv_trans cvftbaseTheory.shade_def

Theorem shade_green = cv_eval “shade (Green 2)”

val _ = assert (aconv “3:num” o rhs o concl) shade_green
