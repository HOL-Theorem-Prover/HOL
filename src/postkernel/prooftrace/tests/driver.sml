val source = valOf (OS.Process.getEnv "HOL_PFT_SOURCE_ROOT") ^
  "/src/postkernel/prooftrace/";
val test_source = source ^ "tests/";
val identity_phase = valOf (OS.Process.getEnv "HOL_PFT_IDENTITY_PHASE");
val () =
  if identity_phase = "produce" then
    use (test_source ^ "identity-produce.sml")
  else
    (List.app load ["DArray","PIntMap","RawTheory_dtype"];
     List.app (fn name =>
       (use (source ^ name ^ ".sig"); use (source ^ name ^ ".sml")))
       ["ProofTraceParser","ProofTraceWalk","ProofTraceReplay"];
     use (test_source ^ (if identity_phase = "raw" then
       "identity-selftest.sml" else "identity-loader.sml")));
val () = print "PFT_TEST_PHASE_PASS\n";
