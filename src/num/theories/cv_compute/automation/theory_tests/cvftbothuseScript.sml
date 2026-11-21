Theory cvftbothuse
Ancestors
  cvftboth
Libs
  cv_transLib

(* cvftleft and cvftright are ancestors of cvftboth, so its translation
   of colour is used without a clash *)

val _ = assert (equal "cvftboth" o #Thy o dest_thy_const)
               (cv_typeLib.from_term_for “:colour”)

val _ = cv_trans cvftbaseTheory.shade_def

Theorem shade_green = cv_eval “shade (Green 2)”

val _ = assert (aconv “3:num” o rhs o concl) shade_green
