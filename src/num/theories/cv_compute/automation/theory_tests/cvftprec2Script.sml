Theory cvftprec2
Ancestors
  cvftrightdup
Libs
  cv_transLib

(* cvftprec1 with cvftpickright's entry first *)

val _ = load "cvftpickrightTheory"

fun first_colour_entry () =
  valOf (List.find (String.isSuffix "colour_thm")
                   (map #1 (cv_memLib.cv_from_to_entries ())))

val _ = assert (String.isPrefix "cvftpickright." o first_colour_entry) ()

fun from_thy ty =
  cv_typeLib.from_term_for ty |> strip_comb |> fst |> dest_thy_const |> #Thy

val _ = assert (equal "cvftright" o from_thy) “:colour”
