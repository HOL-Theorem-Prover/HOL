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

val _ = assert (String.isPrefix "cvftright." o #1 o valOf o
                List.find (String.isSuffix "colour_thm" o #1))
               (cv_memLib.cv_from_to_entries ())

fun from_thy ty =
  cv_typeLib.from_term_for ty |> strip_comb |> fst |> dest_thy_const |> #Thy

fun is_clash e =
  String.isSubstring "cv_from_to_delete" (Feedback.message_of e)

val _ = assert (fn ty => (from_thy ty; false) handle HOL_ERR e => is_clash e)
               “:colour”

(* also when cv_trans checks an argument of function type: with a (test
   only, assumed) translation of bool -> 'a, the clash for colour is
   reported, not taken as a higher-order argument *)
val _ = cv_memLib.cv_from_to_add (mk_thm ([],
  “from_to (f:'a -> cv) (t:cv -> 'a) ==>
   from_to (bf:(bool -> 'a) -> cv) (bt:cv -> bool -> 'a)”))

Definition pick_def:
  pick (f:bool -> colour) = shade (f T)
End

val _ = assert (fn def => (cv_trans def; false) handle HOL_ERR e => is_clash e)
               pick_def

val _ = cv_from_to_delete
          "cvftright.from_cvftbase_to_cvftbase_colour_thm"
val _ = cv_rep_delete "cvftright.cv_rep_cvftbase_cvftbase_colour_datatype"

val _ = assert (equal "cvftleft" o from_thy) “:colour”

val _ = cv_trans cvftbaseTheory.shade_def

Theorem shade_green = cv_eval “shade (Green 2)”

val _ = assert (aconv “3:num” o rhs o concl) shade_green
