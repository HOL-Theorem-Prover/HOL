val source = valOf (OS.Process.getEnv "HOL_PFT_SOURCE_ROOT") ^
  "/src/postkernel/prooftrace/";
val test_source = source ^ "tests/";
val identity_phase = valOf (OS.Process.getEnv "HOL_PFT_IDENTITY_PHASE");
val () =
  if List.exists (fn phase => phase = identity_phase)
       ["produce","import-parent","import-child"] then
    use (test_source ^ "identity-" ^ identity_phase ^ ".sml")
  else
    (List.app load ["DArray","PIntMap","RawTheory_dtype"];
     List.app (fn name =>
       (use (source ^ name ^ ".sig"); use (source ^ name ^ ".sml")))
       ["ProofTraceParser","ProofTraceWalk","ProofTraceReplay"];
     if identity_phase = "role" orelse identity_phase = "custom-role" then
       use (test_source ^ "identity-role-selftest.sml")
     else use (test_source ^ "identity-selftest.sml"));
val () = print "PFT_TEST_PHASE_PASS\n";
