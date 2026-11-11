fun check_oracle_results db = let
  val p = Term.mk_var ("p", Type.bool)
  val q = Term.mk_var ("q", Type.bool)
  val r = Term.mk_var ("r", Type.bool)
  val th = valOf (PFTReplay.lookup db "oracle_hyps$hyps")
in
  if length (Thm.hyp th) = 2 andalso
     List.exists (Term.aconv q) (Thm.hyp th) andalso
     List.exists (Term.aconv r) (Thm.hyp th) andalso
     Term.aconv (Thm.concl th) p
  then print "PFT_ORACLE_ALL_CHECKS_PASSED\n"
  else raise Fail "oracle replay lost hypotheses or changed its conclusion"
end;
