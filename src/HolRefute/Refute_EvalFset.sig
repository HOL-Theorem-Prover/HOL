signature Refute_EvalFset = sig
  val canonical_chain : Term.term -> Term.term
  val is_fset_ty : Type.hol_type -> bool
  val register : unit -> unit
end
