Theory cvftorder
Ancestors
  cvftbase
Libs
  cv_memLib

(* cvftreplay with the theories loaded after cv_memLib *)

val _ = load "cvftpickrightTheory"
val _ = load "cvftbothTheory"
val _ = use "cvftreplay.ML"
