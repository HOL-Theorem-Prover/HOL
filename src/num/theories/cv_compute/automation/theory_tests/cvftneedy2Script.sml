Theory cvftneedy2
Ancestors
  cvftneedy
Libs
  cv_transLib

(* cvftneedy1 with cvftleft's entry first *)

val _ = load "cvftleftTheory"

fun first_colour_entry () =
  valOf (List.find (String.isSuffix "colour_thm")
                   (map #1 (cv_memLib.cv_from_to_entries ())))

val _ = assert (String.isPrefix "cvftleft." o first_colour_entry) ()

fun from_thy ty =
  cv_typeLib.from_term_for ty |> strip_comb |> fst |> dest_thy_const |> #Thy

fun fails_with_clash ty =
  (from_thy ty; false)
  handle HOL_ERR e =>
    String.isSubstring "cv_from_to_delete" (Feedback.message_of e)

val _ = assert fails_with_clash “:colour”
