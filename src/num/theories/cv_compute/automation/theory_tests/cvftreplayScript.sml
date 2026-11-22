Theory cvftreplay
Ancestors
  cvftpickright cvftboth

(* cvftpickright and cvftboth each descend from cvftleft and cvftright;
   cvftboth's name sorts before both, cvftpickright's between them.
   cv_memLib is loaded only now, so it replays the ancestors' cv_from_to
   entries.  The checks are read in with use, since naming cv_memLib in
   this script would have it loaded before the ancestors. *)

val _ = load "cv_memLib"
val _ = use "cvftreplay.ML"
