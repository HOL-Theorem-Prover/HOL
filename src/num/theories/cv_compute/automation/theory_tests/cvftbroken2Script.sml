Theory cvftbroken2
Ancestors
  cvftbroken
Libs
  cv_transLib

(* cvftbroken1 with cvftleft's entry first *)

val _ = load "cvftleftTheory"

fun first_colour_entry () =
  valOf (List.find (String.isSuffix "colour_thm")
                   (map #1 (cv_memLib.cv_from_to_entries ())))

val _ = assert (String.isPrefix "cvftleft." o first_colour_entry) ()

fun from_thy ty =
  cv_typeLib.from_term_for ty |> strip_comb |> fst |> dest_thy_const |> #Thy

val _ = assert (equal "cvftleft" o from_thy) “:colour”
