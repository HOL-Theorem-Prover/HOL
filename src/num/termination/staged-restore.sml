(* Run after the process that wrote staged-checkpoint.save has exited. *)
val finish = valOf (!StagedCheckpoint.pending)
val _ = if !StagedCheckpoint.prefixes = 1 then ()
        else raise Fail "termination prefix was repeated"
val _ = if length (proofManagerLib.top_goals ()) = 1 then ()
        else raise Fail "termination goalstack was not restored"
val _ = if Feedback.current_trace "computeLib.auto_import_definitions" = 0
           andalso Feedback.current_trace "Definition.delete support defs" = 0
        then () else raise Fail "termination flags were not restored"
val _ = proofManagerLib.e
  (Tactic.CONJ_TAC THENL
     [TotalDefn.WF_TAC,
      TotalDefn.TC_SIMP_TAC (TotalDefn.termination_ss ()) []])
val resume_def = finish (proofManagerLib.top_thm ())
val resume_steps = DB.fetch "-" "resume_steps"
fun rename_resume t =
  Term.subst [{redex = “resume_fun”, residue = “baseline_fun”}] t
val _ = if aconv (Thm.concl baseline_def)
                (rename_resume (Thm.concl resume_def)) andalso
           aconv (Thm.concl baseline_steps)
                (rename_resume (Thm.concl resume_steps))
        then () else raise Fail "resumed and native theorems differ"
val _ = if null (Thm.hyp resume_def) andalso
           null (Thm.hyp resume_steps) andalso
           Option.isSome (DefnBase.lookup_indn “resume_fun”) andalso
           Option.isSome (DefnBase.lookup_userdef “resume_fun”) andalso
           #loc (#2 (valOf (DB.lookup {Thy="-",Name="resume_def"}))) =
             StagedCheckpoint.loc
        then () else raise Fail "restored definition was not completed"
val _ = if !StagedCheckpoint.attribute_calls = 1 andalso
           Feedback.current_trace "computeLib.auto_import_definitions" = 0
        then () else raise Fail "completion lost attribute side effects"
val _ = if !Defn.def_suffix = StagedCheckpoint.def_suffix andalso
           !Defn.ind_suffix = StagedCheckpoint.ind_suffix
        then () else raise Fail "definition suffixes leaked"
val _ = if Feedback.current_trace "Definition.delete support defs" = 0
        then () else raise Fail "tactic flag mutation was lost"
val _ = if aconv (boolSyntax.rhs (Thm.concl
             (computeLib.CBV_CONV (computeLib.the_compset ()) “resume_fun 2”)))
                “resume_fun 2”
        then () else raise Fail "nocompute definition entered EVAL"
val _ = (finish (proofManagerLib.top_thm ());
         raise Fail "definition completed twice")
        handle Feedback.HOL_ERR _ => ()
val _ = StagedCheckpoint.mark "finished"
