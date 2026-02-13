(* ProofTrace: build dependency placeholder for KERNELID=tracknl.

   Architecture:
   - During build: Thm module streams step records to per-PID temp files
     (.tracknl_<PID>_steps.log, .tracknl_<PID>_parents.tbl)
   - At export_theory: Thm.trace_export reads temp files, backward
     reachability minimizes from exported theorem roots, writes .pftrace
   - This structure is loaded into hol.state0 via src/proofman/Holmakefile
     as a build dependency, but trace export is handled entirely by the
     kernel (Thm.trace_export) called from Theory.export_theory.

   The trace export was originally split between this structure (for
   Bare/Full build phases) and the kernel (for Initial phase). Since
   the kernel version handles all phases, this structure is now empty.
*)

structure ProofTrace :> ProofTrace =
struct
end
