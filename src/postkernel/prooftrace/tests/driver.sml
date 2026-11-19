val source = valOf (OS.Process.getEnv "HOL_PFT_SOURCE_ROOT") ^
  "/src/postkernel/prooftrace/";
val test_source = source ^ "tests/";
val phase = valOf (OS.Process.getEnv "HOL_PFT_PHASE");
fun pass () = (print "PFT_TEST_PHASE_PASS\n";
               OS.Process.exit OS.Process.success);
fun load_pft extras =
  (List.app load ["DArray","PIntMap","RawTheory_dtype"];
   List.app (fn name =>
     (use (source ^ name ^ ".sig"); use (source ^ name ^ ".sml")))
     (["ProofTraceParser","ProofTraceWalk","PFTOpcodes","PFTWriter",
       "IntPairTable","PFTEmit"] @ extras));
val () = load_pft ["PFTReader","PFTReplay","PFTMerge"];
val () = use (test_source ^ "check.sml");
val rulesets = [("hol4",PFTEmit.HOL4),("candle",PFTEmit.Candle)];
fun emit trace output ruleset =
  PFTEmit.emit_theory {trace=trace,output=output,ruleset=ruleset};
fun convert thy stem = List.app (fn (label,rs) =>
  emit (".hol/objs/" ^ thy ^ "Theory.tr.gz")
    (stem ^ "." ^ label ^ ".pft") rs) rulesets;
fun replay files = List.foldl (fn (file,db) => PFTReplay.replay db file)
  PFTReplay.empty_trDB files;
fun replay_bool files =
  (emit (Systeml.HOLDIR ^ "/src/bool/.hol/objs/boolTheory.tr.gz")
     "hol4/bool.pft" PFTEmit.HOL4;
   replay ("hol4/bool.pft" :: files));
fun save_hyps name hyps expected th =
  (check_sequent name hyps expected th;
   ignore (Theory.save_thm(name,th)));
fun save_exact name = save_hyps name [];
val suite = valOf (OS.Process.getEnv "HOL_PFT_TEST");
val () = use (test_source ^ suite ^ "-selftest.sml");
val () = pass ();
