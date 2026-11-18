Theory stagedTermination
Ancestors stagedTerminationAnc

(* A Termination proof that suspends a goal, resumed after a helper
   theorem; Finalise binds the equations and the named induction theorem *)

Definition staged_def[induction=staged_steps]:
  staged n = if n = 0 then 0n else staged (n - 1) + 1
Termination
  qexists_tac ‘$<’ >> suspend "tc"
End

Theorem staged_tc:
  !n. n <> 0 ==> n - 1 < n
Proof
  DECIDE_TAC
QED

Resume staged_def[tc]:
  markerLib.RESUME_TAC >> conj_tac >- TotalDefn.WF_TAC >>
  metis_tac [staged_tc]
QED

Finalise staged_def

(* Under Holmake --fast the ancestor's theorems are not suspended *)
fun ancestor_kept nm =
  Option.isSome (markerLib.lookup_suspension ("stagedTerminationAnc." ^ nm))
  orelse can (DB.fetch "stagedTerminationAnc") nm

val _ =
  if null (hyp staged_def) andalso null (hyp staged_steps) andalso
     is_forall (concl staged_steps) andalso ancestor_kept "staged_def"
  then () else raise Fail "Finalise did not bind the completed definition"

(* A definition only prepared keeps Resume and Finalise of its name off the
   ancestor's suspended theorem *)
val prepared_goal = valOf (TotalDefn.prepare_qDefine "prepared_def"
  ‘prepared n = if n = 0 then 0n else prepared (n - 1) + 1’)
fun fails_with s f =
  (ignore (f ()); false)
  handle HOL_ERR e => String.isSubstring s (message_of e)
val _ =
  if fails_with "No suspended theorem named prepared_def"
       (fn () => markerLib.resume
                   {suspension_name = "prepared_def", label_name = "tc"}
                   (TRY markerLib.RESUME_TAC >> metis_tac [])
                   (Context.snapshot ())) andalso
     fails_with "No such suspended theorem: prepared_def"
       (fn () => markerLib.finalise_suspended_thm DB.Unknown "prepared_def")
  then () else raise Fail "Resume or Finalise reached the ancestor"
val prepared_def = TotalDefn.complete_definition "prepared_def"
  (TAC_PROOF (prepared_goal, WF_REL_TAC ‘$<’))
val _ =
  if ancestor_kept "prepared_def" then ()
  else raise Fail "the ancestor's suspended theorem was taken"

(* A plain theorem of this theory does not hide an ancestor's suspended
   theorem of the same name from Resume, unless --fast proved it *)
Theorem shadowed:
  T
Proof
  REWRITE_TAC []
QED

val _ =
  case markerLib.lookup_suspension "stagedTerminationAnc.shadowed" of
      NONE => ()
    | SOME _ =>
      if Theory.oracle_string_of shadowed = SOME "FAST-CHEAT" then () else
      (markerLib.resume {suspension_name = "shadowed", label_name = "sh"}
         (rpt strip_tac >> metis_tac []) (Context.snapshot ());
       if null (markerLib.lookup_resumption
                  {parent_thy = "stagedTerminationAnc",
                   parent_name = "shadowed", label = "sh"})
       then raise Fail "Resume missed the ancestor's suspended theorem"
       else ())
