Theory cvftpickd1
Ancestors
  cvftpickd
Libs
  cv_transLib

(* cvftpickd's translation of colour differs from the one cvftrightdup
   gives, and neither theory is an ancestor of the other, so using colour
   is an error, although cvftrightdup's equals that of cvftpickd's
   ancestor cvftpickright.  cvftrightdup is loaded after cv_memLib, so
   its entry comes first; cvftpickd2 tests the other order. *)

val _ = load "cvftrightdupTheory"

fun first_colour_entry () =
  valOf (List.find (String.isSuffix "colour_thm")
                   (map #1 (cv_memLib.cv_from_to_entries ())))

val _ = assert (String.isPrefix "cvftrightdup." o first_colour_entry) ()

fun fails_with_clash ty =
  (cv_typeLib.from_term_for ty; false)
  handle HOL_ERR e =>
    String.isSubstring "cv_from_to_delete" (Feedback.message_of e)

val _ = assert fails_with_clash “:colour”
