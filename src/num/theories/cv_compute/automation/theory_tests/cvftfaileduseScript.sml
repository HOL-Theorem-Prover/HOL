Theory cvftfaileduse
Ancestors
  cvftfaild
Libs
  cv_transLib

(* cvftfaild's translation of colour does not settle the clash between
   those of its ancestors cvftleft and cvftright *)

fun fails_with_clash ty =
  (cv_typeLib.from_term_for ty; false)
  handle HOL_ERR e =>
    String.isSubstring "cv_from_to_delete" (Feedback.message_of e)

val _ = assert fails_with_clash “:colour”
