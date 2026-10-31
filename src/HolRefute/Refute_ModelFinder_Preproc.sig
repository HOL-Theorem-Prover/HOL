signature Refute_ModelFinder_Preproc = sig
  type term = Term.term

  type context = Refute_ModelFinder_HOL.mf_context

  val preprocess_formulas :
    context -> term list -> term ->
    term list * term list * term list * bool * bool * bool
end
