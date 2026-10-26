val () = List.app load ["DArray", "PIntMap", "RawTheory_dtype"];
val source = valOf (OS.Process.getEnv "HOL_PFT_SOURCE_ROOT") ^
  "/src/postkernel/prooftrace/";
fun module name = (use (source ^ name ^ ".sig"); use (source ^ name ^ ".sml"));
val () = List.app module
  ["ProofTraceParser", "ProofTraceWalk", "PFTOpcodes", "PFTWriter",
   "IntPairTable", "PFTCandleComputePreamble", "PFTEmit"];
val () = PFTEmit.emit_expect := true;
val () = List.app (fn (name,ruleset) => (
  PFTEmit.emit_theory
    {trace=".hol/objs/compute_numeralsTheory.tr.gz",
     output="compute_numerals." ^ name ^ ".pft",binary=true,ruleset=ruleset};
  print ("PASS arbitrary-precision compute numerals convert to " ^ name ^
         "\n"))) [("hol4",PFTEmit.HOL4),("candle",PFTEmit.Candle)];
