(* Run by selftest.sml in an isolated Poly/ML process. *)
val _ = load "TotalDefn"
open HolKernel Parse boolLib TotalDefn

val _ = new_theory "staged_checkpoint"

val baseline_def = qDefine "baseline_def[nocompute,induction=baseline_steps]"
  ‘baseline_fun n = if n = 0 then 0n else baseline_fun (n - 1) + 1’
  (SOME (WF_REL_TAC ‘$<’))
val baseline_steps = DB.fetch "-" "baseline_steps"

structure StagedCheckpoint =
struct
  val pending : (thm -> thm) option ref = ref NONE
  val prefixes = ref 0
  val def_suffix = !Defn.def_suffix
  val ind_suffix = !Defn.ind_suffix
  val loc = DB_dtype.mkloc ("checkpoint-test", 17, true)
  val attribute_calls = ref 0
  fun attribute {name,attrname,args,thm} =
    if Feedback.current_trace "computeLib.auto_import_definitions" = 1
    then (attribute_calls := !attribute_calls + 1;
          Feedback.set_trace "computeLib.auto_import_definitions" 0)
    else raise Fail "attribute ran before leaving definition scope"
  fun mark s =
    let val out = TextIO.openAppend "staged-checkpoint.markers"
    in TextIO.output (out,s ^ "\n"); TextIO.closeOut out end
  fun checkpoint g ctxt =
    let
      val _ = pending := current_termination_finisher ctxt
      val _ = if Option.isSome (!pending) then ()
              else raise Fail "termination context has no finisher"
      val _ = mark "prepared"
      val _ = proofManagerLib.set_goal g
      val _ = proofManagerLib.e (Q.EXISTS_TAC ‘$<’)
      val _ = prefixes := !prefixes + 1
      val _ = mark "prefix"
      val _ = Feedback.set_trace "Definition.delete support defs" 0
      val _ = Portable.save_heap "staged-checkpoint.save"
    in OS.Process.exit OS.Process.success end
end

val _ = ThmAttribute.register_attribute
  ("checkpoint_test", {localf = StagedCheckpoint.attribute,
                       storedf = StagedCheckpoint.attribute})
val _ = located_qDefine StagedCheckpoint.loc
  "resume_def[nocompute,induction=resume_steps,checkpoint_test]"
  ‘resume_fun n = if n = 0 then 0n else resume_fun (n - 1) + 1’
  (SOME StagedCheckpoint.checkpoint) (Context.snapshot ())
val _ = raise Fail "checkpoint tactic returned"
