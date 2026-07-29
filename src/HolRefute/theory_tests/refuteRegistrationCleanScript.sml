Theory refuteRegistrationClean
Ancestors
  refuteTableZoo
Libs
  Refute

val _ = Refute.register_typedef
  {ty = ``:zoo_three``, abs = ``zoo_three_abs``, rep = ``zoo_three_rep``,
   absrep_thm = zoo_three_absrep};

(* The default Frac registration is session data and creates no theory
   content.  Its display half is present without an explicit registration. *)
val _ =
  case Refute.lookup_term_postprocessor ``:rat`` of
      SOME _ => ()
    | NONE => raise Fail "default rational Frac registration is missing";

(* The inductive conjunct takes the normal well-foundedness-check path; the
   typedef conjunct takes registration, unfolding, and axiom generation. *)
val result =
  if Refute_Forl.is_configured () then
    SOME
      (Refute.refute
        (Refute.default_config
          |> Refute.upd_backends (SOME ["kodkod"])
          |> Refute.upd_sequential true
          |> Refute.upd_card [(NONE, [2])]
          |> Refute.upd_timeout 10.0
          |> Refute.upd_expect Refute.ExpectGenuine)
        ``zoo_wf_lfp 1 /\
          ((x : zoo_three) = zoo_three_abs 0)``)
  else
    NONE

val _ =
  case result of
      NONE =>
        print "(Kodkodi not configured, registration hygiene skipped.)\n"
    | SOME
        (Refute.Counterexample
          ({backend = "kodkod", substrate = "kodkod", ...} :: _)) => ()
    | SOME _ =>
        raise Fail "MF did not refute the registration-hygiene goal"
