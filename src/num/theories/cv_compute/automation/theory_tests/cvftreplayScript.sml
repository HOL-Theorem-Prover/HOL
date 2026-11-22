Theory cvftreplay
Ancestors
  cvftboth cvftrightdup

(* A theory's cv_from_to entries come before its ancestors' when
   cv_memLib replays them on loading (here: cvftboth's name sorts before
   cvftright's, cvftrightdup's after) and when the theory is loaded after
   cv_memLib.  The checks are read in with use, since naming cv_memLib in
   this script would have it loaded before the ancestors. *)

val _ = load "cv_typeLib"
val _ = use "cvftreplay.ML"
