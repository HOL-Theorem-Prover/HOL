Theory refuteMfClean
Ancestors
  refute
Libs
  Refute

val result =
  if Refute_Forl.is_configured () then
    SOME
      (Refute.refute
        (Refute.default_config
          |> Refute.upd_search (Refute.Only [Refute.ModelFinder])
          |> Refute.upd_sequential true
          |> Refute.upd_card [(NONE, [1, 2])]
          |> Refute.upd_timeout 10.0
          |> Refute.upd_expect Refute.ExpectGenuine)
        ``(b : bool)``)
  else
    NONE

val _ =
  case result of
      NONE =>
        print "(Kodkodi not configured, MF theory-hygiene run skipped.)\n"
    | SOME
        (Refute.Counterexample
          ({backend = "kodkod", substrate = "kodkod", ...} :: _)) => ()
    | SOME _ => raise Fail "MF did not refute the theory-hygiene goal"
