(* Run by selftest.sml in an isolated Poly/ML process. *)
val _ = load "TotalDefn"
open HolKernel Parse boolLib TotalDefn

val _ = new_theory "staged_checkpoint"

structure StagedCheckpoint =
struct
  val pending : prepared_definition option ref = ref NONE
  val prefixes = ref 0
  fun mark s =
    let val out = TextIO.openAppend "staged-checkpoint.markers"
    in TextIO.output (out,s ^ "\n"); TextIO.closeOut out end
  fun driver p tac =
    let
      val _ = pending := SOME p
      val _ = mark "prepared"
      val (_,g) = valOf (termination_goal p)
      val _ = proofManagerLib.set_goal g
      val _ = proofManagerLib.e (Q.EXISTS_TAC ‘$<’)
      val _ = prefixes := !prefixes + 1
      val _ = mark "prefix"
      val _ = Portable.save_heap "staged-checkpoint.save"
    in OS.Process.exit OS.Process.success end
end

val _ =
  (with_termination_driver StagedCheckpoint.driver
     (qDefine "resume_def[nocompute,induction=resume_steps]"
       ‘resume_fun n = if n = 0 then 0n else resume_fun (n - 1) + 1’)
     (SOME (WF_REL_TAC ‘$<’));
   raise Fail "checkpoint driver returned")
