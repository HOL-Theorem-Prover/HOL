Theory cvftprec1
Ancestors
  cvftpickright
Libs
  cv_transLib

(* cvftleft's translation of colour gives way to that of its descendant
   cvftpickright, which is the one the unrelated cvftrightdup gives, so
   there is no clash.  cvftrightdup is loaded after cv_memLib, so its
   entry comes first; cvftprec2 tests the other order. *)

val _ = load "cvftrightdupTheory"

fun first_colour_entry () =
  valOf (List.find (String.isSuffix "colour_thm")
                   (map #1 (cv_memLib.cv_from_to_entries ())))

val _ = assert (String.isPrefix "cvftrightdup." o first_colour_entry) ()

fun from_thy ty =
  cv_typeLib.from_term_for ty |> strip_comb |> fst |> dest_thy_const |> #Thy

val _ = assert (equal "cvftright" o from_thy) “:colour”
