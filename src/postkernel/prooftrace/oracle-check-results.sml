fun check_oracle_results db = let
  val p = Term.mk_var ("p", Type.bool)
  val q = Term.mk_var ("q", Type.bool)
  val r = Term.mk_var ("r", Type.bool)
  val cases =
    [("empty", [], p),
     ("one", [q], p),
     ("two", [q, r], p),
     ("overlap", [p, q], p),
     ("duplicate", [q, r], p)]
  fun subset xs ys = List.all (fn x => List.exists (Term.aconv x) ys) xs
  fun check (name, hyps, concl) = let
    val key = "oracle_hyps$" ^ name
    val th = case PFTReplay.lookup db key of
        SOME th => th
      | NONE => raise Fail ("missing oracle fixture: " ^ key)
    val actual = Thm.hyp th
  in
    if length actual = length hyps andalso
       subset actual hyps andalso subset hyps actual andalso
       Term.aconv (Thm.concl th) concl
    then print ("CHECKED: " ^ key ^ "\n")
    else raise Fail ("wrong oracle sequent: " ^ key)
  end
in List.app check cases; print "PFT_ORACLE_ALL_CHECKS_PASSED\n" end;
