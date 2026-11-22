(* Read in by cvftreplayScript.sml and cvftorderScript.sml: each theory's
   cv_from_to entries come before its ancestors' *)
fun entry_pos thy = let
  fun go _ [] = raise Fail ("no cv_from_to entry from " ^ thy)
    | go i ((n, _)::es) =
        if String.isPrefix (thy ^ ".") n then i else go (i + 1) es
  in go 0 (cv_memLib.cv_from_to_entries ()) end

val _ = assert (fn () =>
  entry_pos "cvftboth" < entry_pos "cvftleft" andalso
  entry_pos "cvftboth" < entry_pos "cvftright" andalso
  entry_pos "cvftpickright" < entry_pos "cvftleft" andalso
  entry_pos "cvftpickright" < entry_pos "cvftright") ()
