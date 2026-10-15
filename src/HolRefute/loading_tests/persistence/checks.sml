open HolKernel Parse boolLib testutils
val _ = Thm.setCT "scratch"
fun check name f =
  (tprint name; if f () then OK () else die name)
fun ty text = Parse.Type [QUOTE (":" ^ text)]
fun accepted f = (f (); true)
  handle HOL_ERR e => (print (Feedback.format_ERR e); false)
fun rejected f = (f (); false) handle HOL_ERR _ => true
val _ = check "exported custom codata survives a fresh process" (fn () =>
  accepted (fn () => Refute.export_registrations [ty "'a persist_codata"]))
val _ = check "anonymous typedef proof survives a fresh process" (fn () =>
  accepted (fn () => Refute.export_registrations [ty "persist_sub"]))
val _ = check "session codata was not persisted" (fn () =>
  rejected (fn () => Refute.export_registrations [ty "'a persist_local"]))
val _ = check "producer has no public bijection binding" (fn () =>
  rejected (fn () => ignore (DB.fetch "refutePersist" "persist_bij")))
val _ = check "persistence does not load optional support" (fn () =>
  not (Lib.mem "rat" (Theory.ancestry "-")) andalso
  not (Lib.mem "real" (Theory.ancestry "-")))
val _ = check "unexported anonymous typedef cannot be discovered" (fn () =>
  rejected (fn () => Refute.export_registrations [ty "persist_control"]))
val _ = check "partial and total quotient descriptions survive import"
  (fn () => accepted (fn () => Refute.export_registrations
    [ty "persist_partial", ty "persist_total", ty "persist_domain"]))
val _ = check "retained harvest proofs and selected discovery survive import"
  (fn () => accepted (fn () => Refute.export_registrations
    [ty "persist_harvested", ty "persist_discovered"]))
val _ = if Lib.mem "refutePersistWrapper" (Theory.ancestry "-") then
  check "wrapper supplies the ancestor operator's description" (fn () =>
    accepted (fn () => Refute.export_registrations [ty "persist_old"]))
  else ()
val semantic_config = Refute.default_config
  |> Refute.upd_search (Refute.Only [Refute.ModelFinder])
  |> Refute.upd_quiet true |> Refute.upd_sequential true
  |> Refute.upd_timeout 30.0
  |> Refute.upd_card [(SOME (ty "persist_domain"), [1]), (NONE, [2])]
  |> Refute.upd_user_axioms (SOME false)
fun term text = Parse.Term [QUOTE text]
val semantic_available = case Refute.refute semantic_config (term "F") of
    Refute.Unknown ["no configured backend"] => false | _ => true
fun semantic_cex text =
  case Refute.refute semantic_config (term text) of
      Refute.Counterexample (_ :: _) => true | _ => false
val _ = if semantic_available then
  check "partial quotient keeps its domain; total quotient admits both bools"
    (fn () => not (semantic_cex "persist_domain_rep d") andalso
              semantic_cex "persist_total_rep d")
else print "(Kodkodi not configured, quotient semantics skipped.)\n"

val _ = check "codata witnesses and two-half typedef inputs survive import"
  (fn () => accepted (fn () => Refute.export_registrations
    [ty "'a persist_stream", ty "persist_halves"]))
val _ = if semantic_available then
  check "exported codata admits cyclic countermodels"
    (fn () => semantic_cex "(s : bool persist_stream) <> persist_scons a s")
else print "(Kodkodi not configured, codata semantics skipped.)\n"
val _ = check "generic typedef descriptions survive import" (fn () =>
  accepted (fn () => Refute.export_registrations [ty "'a persist_generic"]))
val generic_config = semantic_config |> Refute.upd_card
  [(SOME (ty "bool persist_generic"), [4]),
   (SOME (ty "num persist_generic"), [4]), (NONE, [2])]
fun generic_cex text =
  case Refute.refute generic_config (term text) of
      Refute.Counterexample (_ :: _) => true | _ => false
val _ = if semantic_available then
  check "an imported generic typedef works at bool and num instances"
    (fn () => generic_cex "(x : bool persist_generic) = y" andalso
              generic_cex "(x : num persist_generic) = y")
else print "(Kodkodi not configured, generic semantics skipped.)\n"
