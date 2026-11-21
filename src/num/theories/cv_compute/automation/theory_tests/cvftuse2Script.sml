Theory cvftuse2
Ancestors
  cvftright cvftleft
Libs
  cv_transLib

(* cvftuse1 with the parents listed the other way round *)

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
          "cvftleft.from_cvftbase_to_cvftbase_colour_thm"
val _ = cv_rep_delete "cvftleft.cv_rep_cvftbase_cvftbase_colour_datatype"

val _ = assert (equal "cvftright" o from_thy) “:colour”

val _ = cv_trans cvftbaseTheory.shade_def

Theorem shade_green = cv_eval “shade (Green 2)”

val _ = assert (aconv “3:num” o rhs o concl) shade_green
