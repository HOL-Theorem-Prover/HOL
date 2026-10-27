val () = List.app load ["DArray", "PIntMap", "RawTheory_dtype"];
val source = valOf (OS.Process.getEnv "HOL_PFT_SOURCE_ROOT") ^
  "/src/postkernel/prooftrace/";
fun module name = (use (source ^ name ^ ".sig"); use (source ^ name ^ ".sml"));
val () = List.app module
  ["ProofTraceParser", "ProofTraceWalk", "PFTOpcodes", "PFTWriter",
   "IntPairTable", "PFTCandleComputePreamble", "PFTEmit"];
val name = valOf (OS.Process.getEnv "HOL_PFT_EXPORT_CASE");
fun convert (label,ruleset) =
  PFTEmit.emit_theory
    {trace=".hol/objs/pftExport_" ^ name ^ "Theory.tr.gz",
     output=name ^ "." ^ label ^ ".pft",binary=true,ruleset=ruleset};
val () = List.app (fn target =>
  (convert target; print ("EXPORT_CONVERTED " ^ #1 target ^ "\n")))
  [("hol4",PFTEmit.HOL4),("candle",PFTEmit.Candle)];
