val source = valOf (OS.Process.getEnv "HOL_PFT_SOURCE_ROOT") ^
  "/src/postkernel/prooftrace/";
val test_source = source ^ "tests/";
fun load_pft extras =
  (List.app load ["DArray","PIntMap","RawTheory_dtype"];
   List.app (fn name =>
     (use (source ^ name ^ ".sig"); use (source ^ name ^ ".sml")))
     (["ProofTraceParser","ProofTraceWalk","PFTOpcodes","PFTWriter",
       "IntPairTable","PFTCandleComputePreamble","PFTEmit"] @ extras));
val suite = valOf (OS.Process.getEnv "HOL_PFT_TEST");
val identity_phase = valOf (OS.Process.getEnv "HOL_PFT_IDENTITY_PHASE");
val () =
  if suite <> "identity" then use (test_source ^ suite ^ "-selftest.sml")
  else if identity_phase = "produce" then
    use (test_source ^ "identity-produce.sml")
  else
    (load_pft ["PFTReader","PFTReplay","ProofTraceReplay"];
     use (test_source ^ "identity-selftest.sml"));
val () = print "PFT_TEST_PHASE_PASS\n";
