Definition staged_source_def[induction=staged_source_steps]:
  staged_source n = if n = 0 then 0n else staged_source (n - 1) + 1
Termination
  WF_REL_TAC ‘$<’
End

val _ =
  if null (hyp staged_source_def) andalso null (hyp staged_source_steps)
  then () else raise Fail "Definition's SML bindings were lost"
