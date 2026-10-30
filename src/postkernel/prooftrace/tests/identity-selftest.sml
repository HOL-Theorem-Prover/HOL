val () = use (test_source ^ "identity-check.sml");
val identity_bootstrap = Systeml.HOLDIR ^
  "/src/bool/.hol/objs/boolTheory.tr.gz";
fun identity_raw thy = ".hol/objs/" ^ thy ^ "Theory.tr.gz";
val () = ProofTraceReplay.replay identity_bootstrap;
val () = List.app (ProofTraceReplay.replay o identity_raw) identity_cases;
val () = identity_check (fn thy => fn name =>
  Symtab.lookup (#1 (ProofTraceReplay.replayed_thms thy)) name) false;
