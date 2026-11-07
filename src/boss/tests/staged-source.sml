open HolKernel Parse boolLib bossLib

val _ = new_theory "staged_source"
val definition_driver_calls = ref 0
fun definition_driver p tac =
  (definition_driver_calls := !definition_driver_calls + 1;
   case TotalDefn.termination_goal p of
       NONE => NONE
     | SOME (name,g) =>
       SOME (boolLib.prove_named (Context.snapshot ())
                                {name=name, goal=g, tac=tac}))
val _ = TotalDefn.with_termination_driver definition_driver
          QUse.use "tests/stagedSourceScript.sml"
val _ = if !definition_driver_calls = 1 then ()
        else raise Fail "termination driver was not called exactly once"
