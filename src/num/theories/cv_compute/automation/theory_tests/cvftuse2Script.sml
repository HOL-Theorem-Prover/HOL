Theory cvftuse2
Ancestors
  cvftright
Libs
  cv_transLib

(* cvftuse1 with cvftleft's entry first *)

val _ = load "cvftleftTheory"

val _ = assert (String.isPrefix "cvftleft." o #1 o valOf o
                List.find (String.isSuffix "colour_thm" o #1))
               (cv_memLib.cv_from_to_entries ())

fun from_thy ty =
  cv_typeLib.from_term_for ty |> strip_comb |> fst |> dest_thy_const |> #Thy

fun is_clash e =
  String.isSubstring "cv_from_to_delete" (Feedback.message_of e)

val _ = assert (fn ty => (from_thy ty; false) handle HOL_ERR e => is_clash e)
               “:colour”

val _ = cv_from_to_delete
          "cvftleft.from_cvftbase_to_cvftbase_colour_thm"

val _ = assert (equal "cvftright" o from_thy) “:colour”
