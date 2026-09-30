signature Refute_ModelFinder_Mono = sig
  val formulas_monotonic :
    Refute_ModelFinder_HOL.mf_context -> bool -> Type.hol_type ->
    Term.term list * Term.term list -> bool
end

