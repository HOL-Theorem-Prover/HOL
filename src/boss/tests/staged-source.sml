open HolKernel Parse boolLib bossLib

val _ = new_theory "staged_source"
val finisher_calls = ref 0
val source_finisher : (thm -> thm) option ref = ref NONE
fun capture_termination g ctxt =
  (finisher_calls := !finisher_calls + 1;
   source_finisher := TotalDefn.current_termination_finisher ctxt;
   ALL_TAC g ctxt)
val _ = QUse.use "tests/stagedSourceScript.sml"
val _ = if !finisher_calls = 1 andalso Option.isSome (!source_finisher)
        then () else raise Fail "termination context was not captured once"
val _ = (valOf (!source_finisher) TRUTH;
         raise Fail "native completion did not consume the finisher")
        handle HOL_ERR e =>
          if Feedback.top_function_of e = "termination_finisher" andalso
             Feedback.message_of e = "Definition already completed or failed"
          then () else Portable.reraise (HOL_ERR e)
