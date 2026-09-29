signature Refute_Extract = sig
  type term = Term.term

  val with_narrowing_window :
    {first : int, last : int} -> ('a -> 'b) -> 'a -> 'b
  val native_preflight :
    Refute_Core.config -> Refute_Eval.strategy -> Refute_Eval.plan list ->
    term list -> string list
  val extract_problem :
    Refute_EvalSML.extraction_mode -> Refute_Core.config ->
    Refute_Eval.strategy -> Refute_Eval.qc_problem ->
    Refute_EvalSML.extraction_result
end
