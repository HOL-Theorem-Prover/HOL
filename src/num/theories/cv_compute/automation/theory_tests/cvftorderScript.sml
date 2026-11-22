Theory cvftorder
Ancestors
  cvftbase
Libs
  cv_typeLib

(* cvftreplay with the theories loaded after cv_memLib *)

val _ = load "cvftrightdupTheory"
val _ = load "cvftbothTheory"
val _ = use "cvftreplay.ML"
