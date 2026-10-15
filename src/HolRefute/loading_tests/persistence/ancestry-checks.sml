open HolKernel Parse boolLib testutils
val _ = print ("diamond parent order: " ^ String.concatWith ", "
  (Theory.parents "refutePersistDiamond") ^ "\n")
val _ = Thm.setCT "scratch"
val cfg = Refute.default_config
  |> Refute.upd_search (Refute.Only [Refute.ModelFinder])
  |> Refute.upd_sequential true |> Refute.upd_quiet true
  |> Refute.upd_timeout 30.0 |> Refute.upd_card [(NONE, [1, 2])]
  |> Refute.upd_user_axioms (SOME false)
fun tm s = Parse.Term [QUOTE s]
fun check name f = (tprint name; if f () then OK () else die name)
fun counterexample goal =
  case Refute.refute cfg (tm goal) of
      Refute.Counterexample (_ :: _) => true | _ => false
val configured = case Refute.refute cfg (tm "F") of
    Refute.Unknown ["no configured backend"] => false | _ => true
val _ = if not configured then
  print "(Kodkodi not configured, ancestry semantics skipped.)\n"
else
  (check "diamond keeps the framework's effective sibling codata case"
     (fn () => not (counterexample
        "persist_old_case_b (persist_old_b s) (\\_. T)"));
   check "diamond does not keep the earlier sibling codata case"
     (fn () => counterexample
        "persist_old_case_a (persist_old_a s) (\\_. T)"))
