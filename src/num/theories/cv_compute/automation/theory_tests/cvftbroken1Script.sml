Theory cvftbroken1
Ancestors
  cvftleft
Libs
  cv_transLib

(* cvftbroken's translation of colour needs one of fnbox, which cannot
   be defined.  Premises are not proved when translations are compared,
   so it still differs from cvftleft's, and using colour is an error.
   cvftbroken is loaded after cv_memLib, so its entry comes first;
   cvftbroken2 tests the other order. *)

val _ = load "cvftbrokenTheory"

fun first_colour_entry () =
  valOf (List.find (String.isSuffix "colour_thm")
                   (map #1 (cv_memLib.cv_from_to_entries ())))

val _ = assert (String.isPrefix "cvftbroken." o first_colour_entry) ()

fun fails_with_clash ty =
  (cv_typeLib.from_term_for ty; false)
  handle HOL_ERR e =>
    String.isSubstring "cv_from_to_delete" (Feedback.message_of e)

val _ = assert fails_with_clash “:colour”
