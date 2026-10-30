open HolKernel Parse boolLib testutils
val _ = Thm.setCT "scratch"
val cfg = Refute.default_config
  |> Refute.upd_search (Refute.Only [Refute.ModelFinder])
  |> Refute.upd_quiet true |> Refute.upd_sequential true
  |> Refute.upd_timeout 30.0 |> Refute.upd_card [(NONE, [2])]
fun tm s = Parse.Term [QUOTE s]
val configured = case Refute.refute cfg (tm "F") of
    Refute.Unknown ["no configured backend"] => false | _ => true
val _ = if configured then
  (tprint "imported descriptions precede an earlier harvested registration";
   case Refute.refute cfg (tm "(x : persist_cross) = y") of
       Refute.Counterexample ({bindings, ...} :: _) =>
         if not (null bindings) andalso List.all (fn (_, value) =>
             String.isSubstring "persist_preferred_abs"
               (Parse.term_to_string value)) bindings
         then OK () else die "the cached harvest shadowed the import"
     | _ => die "the imported typedef did not produce a model")
else print "(Kodkodi not configured, precedence semantics skipped.)\n"
