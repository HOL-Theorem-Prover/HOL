Theory cvftchild
Ancestors
  cvftuse1
Libs
  cv_transLib

(* cvftuse1's choice of cvftleft's translation of colour holds here *)

val _ = assert (equal "cvftleft" o #Thy o dest_thy_const)
               (cv_typeLib.from_term_for “:colour”)

Theorem shade_red = cv_eval “shade Red”

val _ = assert (aconv “0:num” o rhs o concl) shade_red
