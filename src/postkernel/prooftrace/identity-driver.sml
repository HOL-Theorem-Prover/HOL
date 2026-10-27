val identity_source = case OS.Process.getEnv "HOL_PFT_SOURCE_ROOT" of
    SOME root => root ^ "/src/postkernel/prooftrace/"
  | NONE => raise Fail "run identity-tests.sh";
val identity_phase = valOf (OS.Process.getEnv "HOL_PFT_IDENTITY_PHASE");
val () = print ("IDENTITY_PRODUCER_KERNEL " ^ Thm.kernelid ^ "\n");
val () = print ("IDENTITY_PRODUCER_POLY " ^
  Int.toString PolyML.Compiler.compilerVersionNumber ^ "\n");
fun identity_module name =
  (use (identity_source ^ name ^ ".sig");
   use (identity_source ^ name ^ ".sml"));
val () =
  if List.exists (fn phase => phase = identity_phase)
       ["produce","import-parent","import-child"] then
    use (identity_source ^ "identity-" ^ identity_phase ^ ".sml")
  else
    (List.app load ["DArray","PIntMap","RawTheory_dtype"];
     List.app identity_module
       ["ProofTraceParser","ProofTraceWalk","PFTOpcodes","PFTWriter",
        "IntPairTable","PFTCandleComputePreamble","PFTEmit","PFTReader",
        "PFTReplay","ProofTraceReplay","PFTMerge"];
     if identity_phase = "role" orelse identity_phase = "custom-role" then
       use (identity_source ^ "identity-" ^ identity_phase ^ "-selftest.sml")
     else use (identity_source ^ "identity-selftest.sml"));
