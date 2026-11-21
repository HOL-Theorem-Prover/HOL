Theory cvftneedy1
Ancestors
  cvftleft
Libs
  cv_transLib

(* cvftneedy's translation of colour applies once tint has one, which
   asking for colour defines, and differs from cvftleft's.  cvftneedy is
   loaded after cv_memLib, so its entry comes first; cvftneedy2 tests the
   other order. *)

val _ = load "cvftneedyTheory"

fun first_colour_entry () =
  valOf (List.find (String.isSuffix "colour_thm")
                   (map #1 (cv_memLib.cv_from_to_entries ())))

val _ = assert (String.isPrefix "cvftneedy." o first_colour_entry) ()

fun from_thy ty =
  cv_typeLib.from_term_for ty |> strip_comb |> fst |> dest_thy_const |> #Thy

fun fails_with_clash ty =
  (from_thy ty; false)
  handle HOL_ERR e =>
    String.isSubstring "cv_from_to_delete" (Feedback.message_of e)

val _ = assert fails_with_clash “:colour”
