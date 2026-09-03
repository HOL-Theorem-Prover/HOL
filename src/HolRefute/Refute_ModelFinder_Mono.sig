signature REFUTE_MODEL_FINDER_MONO = sig
  val trace : bool ref
  (* The gate and the serialized emission for everything [trace] governs,
     so that a caller outside this module reports through the same one. *)
  val trace_msg : (unit -> string) -> unit
  val formulas_monotonic :
    Refute_ModelFinder_HOL.mf_context -> bool -> Type.hol_type ->
    Term.term list * Term.term list -> bool
end

