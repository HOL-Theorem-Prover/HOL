val () = use (test_source ^ "identity-check.sml");
val identity_order = "identity_parent" :: identity_cases @ ["identity_child"];
val identity_bootstrap = Systeml.HOLDIR ^
  "/src/bool/.hol/objs/boolTheory.tr.gz";
fun identity_raw thy = ".hol/objs/" ^ thy ^ "Theory.tr.gz";
fun identity_reject action prefix =
  if ((action (); false) handle Fail message => String.isPrefix prefix message)
  then print ("IDENTITY_REJECTED " ^ prefix ^ "\n")
  else raise Fail ("expected unsupported identity: " ^ prefix);
val identity_unsupported =
  [("identity_unrecorded","ProofTraceParser: unrecorded imported symbol"),
   ("identity_retired_import","ProofTraceParser: retired imported symbol"),
   ("identity_foreign_definition","ProofTraceWalk: foreign definition from")];
val () =
    (ProofTraceReplay.replay identity_bootstrap;
     List.app (ProofTraceReplay.replay o identity_raw) identity_order;
     identity_check (fn thy => fn name =>
       Symtab.lookup (#1 (ProofTraceReplay.replayed_thms thy)) name) false;
     List.app (fn (thy,prefix) => identity_reject
       (fn () => ProofTraceReplay.replay (identity_raw thy)) prefix)
       identity_unsupported);
