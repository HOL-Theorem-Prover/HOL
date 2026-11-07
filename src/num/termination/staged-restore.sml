(* Run after the process that wrote staged-checkpoint.save has exited. *)
val p = valOf (!StagedCheckpoint.pending)
val _ = if !StagedCheckpoint.prefixes = 1 then ()
        else raise Fail "termination prefix was repeated"
val _ = if length (proofManagerLib.top_goals ()) = 1 then ()
        else raise Fail "termination goalstack was not restored"
val _ = TotalDefn.with_prepared_definition p
  (fn () =>
     if Feedback.current_trace "computeLib.auto_import_definitions" = 0
     then proofManagerLib.e
       (Tactic.CONJ_TAC THENL
          [TotalDefn.WF_TAC,
           TotalDefn.TC_SIMP_TAC (TotalDefn.termination_ss ()) []])
     else raise Fail "termination flags were not restored") ()
val (resume_def,ind) = TotalDefn.finish_definition p
                       (SOME (proofManagerLib.top_thm ()))
val resume_steps = valOf ind
val _ = if null (Thm.hyp resume_def) andalso
           Option.isSome (DB.lookup {Thy="-",Name="resume_def"}) andalso
           Option.isSome (DB.lookup {Thy="-",Name="resume_steps"}) andalso
           Option.isSome (DefnBase.lookup_indn “resume_fun”)
        then () else raise Fail "restored definition was not completed"
val _ = if Feedback.current_trace "computeLib.auto_import_definitions" = 1
        then () else raise Fail "termination flags leaked"
val _ = (TotalDefn.finish_definition p NONE;
         raise Fail "definition completed twice")
        handle Feedback.HOL_ERR _ => ()
val _ = StagedCheckpoint.mark "finished"
