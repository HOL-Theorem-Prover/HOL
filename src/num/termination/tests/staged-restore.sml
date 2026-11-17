(* Run by selftest.sml in a fresh process on the heap staged-save.sml
   saved: finishes the termination proof and completes the definition. *)
fun check (s, b) = if b then () else raise Fail s
val _ = proofManagerLib.e
  (Tactic.CONJ_TAC THENL
     [TotalDefn.WF_TAC,
      TotalDefn.TC_SIMP_TAC (TotalDefn.termination_ss ()) []])
val resume_def =
    TotalDefn.complete_definition "resume_def" (proofManagerLib.top_thm ())
val resume_steps = DB.fetch "-" "resume_steps"
val _ = check ("theorems have hypotheses",
               null (Thm.hyp resume_def) andalso null (Thm.hyp resume_steps))
val _ = check ("definition not registered",
               Option.isSome (DefnBase.lookup_indn “resume_fun”) andalso
               Option.isSome (DefnBase.lookup_userdef “resume_fun”))
val _ = check ("flags not restored",
               HOLFlags.get_bflag computeLib.auto_import_definitions)
val _ = check ("nocompute definition entered EVAL",
  aconv (boolSyntax.rhs (Thm.concl
    (computeLib.CBV_CONV (computeLib.the_compset ()) “resume_fun 2”)))
    “resume_fun 2”)
val _ = check ("definition completed twice",
  (TotalDefn.complete_definition "resume_def" (proofManagerLib.top_thm ());
   false) handle Feedback.HOL_ERR _ => true)
