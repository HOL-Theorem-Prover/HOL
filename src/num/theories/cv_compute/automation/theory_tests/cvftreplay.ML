(* Read in by cvftreplayScript.sml *)
fun entry_pos thy = let
  fun go _ [] = raise Fail ("no cv_from_to entry from " ^ thy)
    | go i ((n, _)::es) =
        if String.isPrefix (thy ^ ".") n then i else go (i + 1) es
  in go 0 (cv_memLib.cv_from_to_entries ()) end

(* cvftboth and cvftrightdup, replayed when cv_memLib was loaded *)
val _ = assert (fn () =>
  entry_pos "cvftboth" < entry_pos "cvftright" andalso
  entry_pos "cvftrightdup" < entry_pos "cvftright") ()

(* cvftrightdup2, loaded after cv_memLib *)
val _ = load "cvftrightdup2Theory"
val _ = assert (fn () => entry_pos "cvftrightdup2" < entry_pos "cvftright") ()

(* cvftrightdup and cvftrightdup2 register the same theorem, and are
   unrelated, which is no clash *)
val _ = cv_memLib.cv_from_to_delete
          "cvftboth.from_cvftbase_to_cvftbase_colour_thm"
val _ = assert (equal "cvftright" o #Thy o dest_thy_const)
               (cv_typeLib.from_term_for (Parse.Type [QUOTE ":colour"]))
