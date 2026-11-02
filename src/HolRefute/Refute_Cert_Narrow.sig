signature Refute_Cert_Narrow = sig
  type term = Term.term

  val certify_case_tree :
    {case_tree : Refute_Eval.case_tree,
     cex : Refute_Core.counterexample,
     env : (term * term) list,
     evals : term list,
     original : term,
     run_depth : int} ->
    Refute_Cert.result
end
