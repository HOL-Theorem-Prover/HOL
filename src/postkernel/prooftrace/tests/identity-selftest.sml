val () = use (test_source ^ "identity-check.sml");
val identity_order = "identity_parent" :: identity_cases @ ["identity_child"];
val identity_bootstrap = Systeml.HOLDIR ^
  "/src/bool/.hol/objs/boolTheory.tr.gz";
fun identity_raw thy = ".hol/objs/" ^ thy ^ "Theory.tr.gz";
fun identity_out thy = "hol4/" ^ thy ^ ".pft.bin";
fun identity_reject action prefix =
  if ((action (); false) handle Fail message => String.isPrefix prefix message)
  then print ("IDENTITY_REJECTED " ^ prefix ^ "\n")
  else raise Fail ("expected unsupported identity: " ^ prefix);
val identity_unsupported =
  [("identity_unrecorded","ProofTraceParser: unrecorded imported symbol"),
   ("identity_retired_import","ProofTraceParser: retired imported symbol"),
   ("identity_foreign_definition","ProofTraceWalk: foreign definition from")];
val () =
  if identity_phase = "convert" then
    let
      fun convert thy raw = PFTEmit.emit_theory
        {trace=raw,output=identity_out thy,ruleset=PFTEmit.HOL4}
      val () = convert "bool" identity_bootstrap
      val () = List.app (fn thy => convert thy (identity_raw thy)) identity_order
      val () = List.app (fn (thy,prefix) =>
        identity_reject (fn () => convert thy (identity_raw thy)) prefix)
        identity_unsupported
    in print "IDENTITY_CONVERSION_PASS\n" end
  else if identity_phase = "raw" then
    (ProofTraceReplay.replay identity_bootstrap;
     List.app (ProofTraceReplay.replay o identity_raw) identity_order;
     identity_check (fn thy => fn name =>
       Symtab.lookup (#1 (ProofTraceReplay.replayed_thms thy)) name) false;
     List.app (fn (thy,prefix) => identity_reject
       (fn () => ProofTraceReplay.replay (identity_raw thy)) prefix)
       identity_unsupported)
  else if identity_phase = "separate" then
    let val inputs = map identity_out ("bool" :: identity_order)
        val db = List.foldl (fn (file,db) => PFTReplay.replay db file)
                   PFTReplay.empty_trDB inputs
    in identity_check (fn thy => fn name =>
         PFTReplay.lookup db (thy ^ "$" ^ name)) false
    end
  else raise Fail ("unknown identity phase: " ^ identity_phase);
