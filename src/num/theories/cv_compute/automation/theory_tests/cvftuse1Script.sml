Theory cvftuse1
Ancestors
  cvftleft
Libs
  cv_transLib

(* cvftleft and cvftright translate colour differently, and neither is an
   ancestor of the other, so using the translation is an error until one
   of them is removed.  cvftright is loaded after cv_memLib, so its entry
   comes first; cvftuse2 tests the other order. *)

val _ = load "cvftrightTheory"

fun first_colour_entry () =
  valOf (List.find (String.isSuffix "colour_thm")
                   (map #1 (cv_memLib.cv_from_to_entries ())))

val _ = assert (String.isPrefix "cvftright." o first_colour_entry) ()

fun from_thy ty =
  cv_typeLib.from_term_for ty |> strip_comb |> fst |> dest_thy_const |> #Thy

fun fails_with_clash ty =
  (from_thy ty; false)
  handle HOL_ERR e =>
    String.isSubstring "cv_from_to_delete" (Feedback.message_of e)

val _ = assert fails_with_clash “:colour”
(* also when colour is the argument of another type's translation *)
val _ = assert fails_with_clash “:num |-> colour”

val _ = cv_from_to_delete
          "cvftright.from_cvftbase_to_cvftbase_colour_thm"
val _ = cv_rep_delete "cvftright.cv_rep_cvftbase_cvftbase_colour_datatype"

val _ = assert (equal "cvftleft" o from_thy) “:colour”

val _ = cv_trans cvftbaseTheory.shade_def

Theorem shade_green = cv_eval “shade (Green 2)”

val _ = assert (aconv “3:num” o rhs o concl) shade_green
