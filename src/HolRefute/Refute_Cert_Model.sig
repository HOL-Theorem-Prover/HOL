signature Refute_Cert_Model = sig
  type term = Term.term

  datatype result =
      Certified of Thm.thm
    | NoCertificate of string
    | DiscardedByWholeFormulaEval

  datatype failure_kind =
      NoProof
    | MalformedInput
    | TrustRejected
    | FuelExhausted
    | DeadlineExhausted
    | InternalFailure

  type failure =
    {kind : failure_kind,
     stage : string,
     depth : int,
     detail : string}

  type provenance = Refute_Skolem.info

  datatype replay_hint_source =
      SkolemValue
    | TypeValue
    | DirectHint

  type replay_hint =
    {term : term,
     source : replay_hint_source,
     provenance : provenance option}

  type policy =
    {total_fuel : int,
     max_generated_candidates : int,
     max_attempted_candidates : int,
     max_completion_candidates : int,
     max_completion_vectors : int,
     max_function_states : int,
     max_constructor_depth : int,
     max_constructor_width : int,
     max_constructor_size : int,
     max_split_depth : int,
     max_case_branches : int,
     max_inductions : int,
     max_leaf_rounds : int}

  type diagnostics =
    {generated_candidates : int,
     function_states : int,
     attempted_candidates : int,
     case_branches : int,
     induction_attempts : int,
     schematic_attempts : int,
     completion_attempts : int,
     candidate_trace : (int * term * term) list,
     consumed_fuel : int,
     failure : failure option}

  val replay_candidate_limit : int
  val default_policy : int -> policy
  val certify_portfolio_detailed_rich :
    {deadline : Time.time option,
     env : (term * term) list,
     hints : replay_hint list,
     holes : term list,
     original : term,
     policy : policy} ->
    result * diagnostics
end
