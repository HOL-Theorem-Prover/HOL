val source = valOf (OS.Process.getEnv "HOL_PFT_SOURCE_ROOT") ^
  "/src/postkernel/prooftrace/";
val () = use (source ^ "oracle-produce.sml");
val () = List.app load ["DArray", "PIntMap", "RawTheory_dtype"];
fun module name = (use (source ^ name ^ ".sig"); use (source ^ name ^ ".sml"));
val () = List.app module
  ["ProofTraceParser", "ProofTraceWalk", "PFTOpcodes", "PFTWriter",
   "IntPairTable", "PFTCandleComputePreamble", "PFTEmit", "PFTReader",
   "PFTMerge", "PFTReplay"];
val () = use (source ^ "oracle-check-results.sml");

val separate = "oracle_hyps.pft.bin";
val merged = "oracle_merged.pft.bin";
val () = PFTEmit.emit_theory
  {trace=".hol/objs/oracle_hypsTheory.tr.gz", output=separate,
   binary=true, ruleset=PFTEmit.HOL4};
val () = check_oracle_results
  (PFTReplay.replay PFTReplay.empty_trDB separate);
val () = PFTMerge.merge
  {inputs=[separate], targets=[PFTMerge.ThyAll ("oracle_hyps", false)],
   output=merged, binary=true};
val () = check_oracle_results
  (PFTReplay.replay PFTReplay.empty_trDB merged);
val unsupported = "deduct_unsupported.pft.bin";
val rejected = (PFTEmit.emit_theory
  {trace=".hol/objs/deduct_antisymTheory.tr.gz", output=unsupported,
   binary=true, ruleset=PFTEmit.HOL4}; false)
  handle Fail msg => msg = "PFTEmit: HOL4 deductAntisym replay unsupported";
val () = if rejected then ()
  else raise Fail "HOL4 export accepted unsupported deductAntisym";
val () = List.app OS.FileSys.remove [separate, merged, unsupported];
val () = print "PFT_ORACLE_SELFTEST_PASSED\n";
