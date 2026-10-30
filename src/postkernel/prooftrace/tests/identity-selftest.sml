val () = use (test_source ^ "identity-check.sml");
val identity_order = identity_cases;
val identity_bootstrap = Systeml.HOLDIR ^
  "/src/bool/.hol/objs/boolTheory.tr.gz";
fun identity_raw thy = ".hol/objs/" ^ thy ^ "Theory.tr.gz";
fun identity_out thy = "hol4/" ^ thy ^ ".pft.bin";
val () =
  if identity_phase = "convert" then
    let
      fun convert thy raw = PFTEmit.emit_theory
        {trace=raw,output=identity_out thy,ruleset=PFTEmit.HOL4}
      val () = convert "bool" identity_bootstrap
      val () = List.app (fn thy => convert thy (identity_raw thy)) identity_order
    in print "IDENTITY_CONVERSION_PASS\n" end
  else if identity_phase = "raw" then
    (ProofTraceReplay.replay identity_bootstrap;
     List.app (ProofTraceReplay.replay o identity_raw) identity_order;
     identity_check (fn thy => fn name =>
       Symtab.lookup (#1 (ProofTraceReplay.replayed_thms thy)) name) false)
  else if identity_phase = "separate" then
    let val inputs = map identity_out ("bool" :: identity_order)
        val db = List.foldl (fn (file,db) => PFTReplay.replay db file)
                   PFTReplay.empty_trDB inputs
    in identity_check (fn thy => fn name =>
         PFTReplay.lookup db (thy ^ "$" ^ name)) false
    end
  else raise Fail ("unknown identity phase: " ^ identity_phase);
