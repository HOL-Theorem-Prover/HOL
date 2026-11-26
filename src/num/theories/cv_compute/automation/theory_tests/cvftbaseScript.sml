Theory cvftbase
Ancestors
  cv_std
Libs
  cv_transLib

(* Shared ancestor for the cv_from_to clash tests: cvftleft and cvftright
   each give colour a from/to translation of their own *)

Datatype:
  colour = Red | Green num
End

Definition shade_def:
  shade c = case c of Red => 0n | Green n => n + 1
End
