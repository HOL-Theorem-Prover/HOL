Theory cvftloopuse2
Ancestors
  cvftleft
Libs
  cv_transLib

(* cvftloopuse with cvftloop's entry first *)

val _ = load "cvftloopTheory"

fun first_colour_entry () =
  valOf (List.find (String.isSuffix "colour_thm")
                   (map #1 (cv_memLib.cv_from_to_entries ())))

val _ = assert (String.isPrefix "cvftloop." o first_colour_entry) ()

fun from_thy ty =
  cv_typeLib.from_term_for ty |> strip_comb |> fst |> dest_thy_const |> #Thy

val _ = assert (equal "cvftleft" o from_thy) “:colour”
