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

val _ =
  if null (hyp staged_def) andalso null (hyp staged_steps) andalso
     is_forall (concl staged_steps) andalso
     Option.isSome
       (markerLib.lookup_suspension "stagedTerminationAnc.staged_def")
  then () else raise Fail "Finalise did not bind the completed definition"
