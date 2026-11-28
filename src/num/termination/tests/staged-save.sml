(* Run by selftest.sml in a fresh process: prepares a definition, starts
   its termination proof and saves a heap that staged-restore.sml
   continues from. *)
val _ = load "TotalDefn"
open HolKernel Parse boolLib TotalDefn

val _ = new_theory "staged_save"
val goal = valOf (prepare_qDefine
  "resume_def[nocompute,induction=resume_steps]"
  ‘resume_fun n = if n = 0 then 0n else resume_fun (n - 1) + 1’)
val _ = proofManagerLib.set_goal goal
val _ = proofManagerLib.e (Q.EXISTS_TAC ‘$<’)
val _ = Portable.save_heap "staged-termination.save"
