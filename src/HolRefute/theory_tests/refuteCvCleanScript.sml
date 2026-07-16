Theory refuteCvClean
Ancestors
  refute_cv
Libs
  Refute

Datatype:
  clean_tree = CleanLeaf num | CleanNode clean_tree clean_tree
End

val config =
  Refute.default_config
  |> Refute.upd_substrate Refute.Cv
  |> Refute.upd_backends (SOME ["exhaustive"])
  |> Refute.upd_sequential true
  |> Refute.upd_size 3
  |> Refute.upd_timeout 10.0

val result = Refute.refute config
  ``(tree : clean_tree) = CleanLeaf 0``

val _ =
  case result of
      Refute.Counterexample
        ({substrate = "cv", cert = SOME _, ...} :: _) => ()
    | _ => raise Fail "cv did not certify the export-cleanliness goal"
