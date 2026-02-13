signature ProofTrace =
sig
  (* ProofTrace is loaded into hol.state0 when KERNELID=tracknl.
     The actual trace export logic lives in the kernel (Thm.trace_export)
     and is called directly by Theory.export_theory. This structure
     exists as a build dependency placeholder. *)
end
