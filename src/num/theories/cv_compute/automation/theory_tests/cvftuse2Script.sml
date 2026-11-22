Theory cvftuse2
Ancestors
  cvftright
Libs
  cv_transLib

(* cvftuse1 with cvftleft's entry first *)

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
(* also when colour is the argument of another type's translation *)
val _ = assert fails_with_clash “:num |-> colour”

(* an entry added here that matches colour but does not apply there (its
   premise needs a translation of a function type) does not settle it *)
val _ = cv_memLib.cv_from_to_add (mk_thm ([],
  “from_to (f:(num -> num) -> cv) t ==>
   from_to (cf:colour -> cv) (ct:cv -> colour)”))

val _ = assert fails_with_clash “:colour”

val _ = cv_from_to_delete
          "cvftleft.from_cvftbase_to_cvftbase_colour_thm"
val _ = cv_rep_delete "cvftleft.cv_rep_cvftbase_cvftbase_colour_datatype"

val _ = assert (equal "cvftright" o from_thy) “:colour”

val _ = cv_trans cvftbaseTheory.shade_def

Theorem shade_green = cv_eval “shade (Green 2)”

val _ = assert (aconv “3:num” o rhs o concl) shade_green
