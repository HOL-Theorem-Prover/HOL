Theory cvftreplay
Ancestors
  cvftboth cvftrightdup

(* cvftboth and cvftrightdup each descend from cvftright (cvftboth
   removed cvftleft's entry); cvftboth's name sorts before cvftright's,
   cvftrightdup's after.  cv_memLib is loaded only now, so it replays
   the ancestors' cv_from_to entries.  The checks are read in with use,
   since naming cv_memLib in this script would have it loaded before the
   ancestors. *)

val _ = load "cv_typeLib"
val _ = use "cvftreplay.ML"
