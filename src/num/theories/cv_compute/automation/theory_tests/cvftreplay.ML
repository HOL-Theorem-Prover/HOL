(* Read in by cvftreplayScript.sml and cvftorderScript.sml: each theory's
   cv_from_to entries come before its ancestors', and the translation of
   a descendant is used over its ancestor's *)
fun entry_pos thy = let
  fun go _ [] = raise Fail ("no cv_from_to entry from " ^ thy)
    | go i ((n, _)::es) =
        if String.isPrefix (thy ^ ".") n then i else go (i + 1) es
  in go 0 (cv_memLib.cv_from_to_entries ()) end

val _ = assert (fn () =>
  entry_pos "cvftboth" < entry_pos "cvftright" andalso
  entry_pos "cvftrightdup" < entry_pos "cvftright") ()

(* cvftboth's and cvftrightdup's translations clash; keep cvftboth's *)
val _ = cv_memLib.cv_from_to_delete "cvftrightdup.dup_colour_thm"

val _ = assert (equal "cvftboth" o #Thy o dest_thy_const)
               (cv_typeLib.from_term_for (Parse.Type [QUOTE ":colour"]))
