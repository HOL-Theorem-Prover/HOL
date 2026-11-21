Theory cvftbroken1
Ancestors
  cvftleft
Libs
  cv_transLib

(* cvftbroken's translation of colour does not apply, since fnbox has no
   translation and defining one fails, so cvftleft's is used.  cvftbroken
   is loaded after cv_memLib, so its entry comes first; cvftbroken2 tests
   the other order. *)

val _ = load "cvftbrokenTheory"

fun first_colour_entry () =
  valOf (List.find (String.isSuffix "colour_thm")
                   (map #1 (cv_memLib.cv_from_to_entries ())))

val _ = assert (String.isPrefix "cvftbroken." o first_colour_entry) ()

fun from_thy ty =
  cv_typeLib.from_term_for ty |> strip_comb |> fst |> dest_thy_const |> #Thy

val _ = assert (equal "cvftleft" o from_thy) “:colour”
