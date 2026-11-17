Definition staged_source_def[induction=staged_source_steps]:
  staged_source n = if n = 0 then 0n else staged_source (n - 1) + 1
Termination
  qexists_tac ‘$<’ >> suspend "tc"
End

Theorem staged_source_tc:
  !n. n <> 0 ==> n - 1 < n
Proof
  DECIDE_TAC
QED

Resume staged_source_def[tc]:
  markerLib.RESUME_TAC >> conj_tac >- TotalDefn.WF_TAC >>
  metis_tac [staged_source_tc]
QED

Finalise staged_source_def

val _ =
  if null (hyp staged_source_def) andalso null (hyp staged_source_steps) andalso
     is_forall (concl staged_source_steps)
  then () else raise Fail "Finalise did not bind the completed definition"
