open HolKernel Parse boolLib testutils
val _ = Thm.setCT "scratch"
val cfg = Refute.default_config
  |> Refute.upd_search (Refute.Only [Refute.ModelFinder])
  |> Refute.upd_quiet true |> Refute.upd_sequential true
  |> Refute.upd_timeout 30.0 |> Refute.upd_card [(NONE, [1, 2])]
  |> Refute.upd_user_axioms (SOME false)
fun tm s = Parse.Term [QUOTE s]
val configured = case Refute.refute cfg (tm "F") of
    Refute.Unknown ["no configured backend"] => false | _ => true
val expected = case OS.Process.getEnv "REFUTE_EXPECT_CASE" of
    SOME "a" => "a" | SOME "b" => "b"
  | _ => raise Fail "the replacement harness did not select a version"
val other = if expected = "a" then "b" else "a"
fun cex case_name =
  case Refute.refute cfg (tm
    ("persist_old_case_" ^ case_name ^ " (persist_old_" ^ case_name ^
     " s) (\\_. T)")) of
      Refute.Counterexample (_ :: _) => true | _ => false
val _ = if configured then
  (tprint ("rebuilt metadata selects case " ^ expected);
   if not (cex expected) andalso cex other then OK ()
   else die "the consumer saw stale replacement metadata")
else print "(Kodkodi not configured, replacement semantics skipped.)\n"
