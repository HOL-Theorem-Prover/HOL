Theory cvftpickd2
Ancestors
  cvftrightdup
Libs
  cv_transLib

(* cvftpickd1 with cvftpickd's entry first *)

val _ = load "cvftpickdTheory"

fun first_colour_entry () =
  valOf (List.find (String.isSuffix "colour_thm")
                   (map #1 (cv_memLib.cv_from_to_entries ())))

val _ = assert (String.isPrefix "cvftpickd." o first_colour_entry) ()

fun fails_with_clash ty =
  (cv_typeLib.from_term_for ty; false)
  handle HOL_ERR e =>
    String.isSubstring "cv_from_to_delete" (Feedback.message_of e)

val _ = assert fails_with_clash “:colour”
