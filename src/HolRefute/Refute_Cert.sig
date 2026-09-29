signature Refute_Cert = sig
  type term = Term.term

  datatype result =
      Certified of Refute_Core.counterexample
    | Uncertified of Refute_Core.counterexample
    | Potential of Refute_Core.counterexample
    | Discarded

  val instantiate : (term * term) list -> term -> term
  val rhs_of : Thm.thm -> term

  datatype instance_verdict =
      InstanceFalse of Thm.thm
    | InstanceTrue
    | InstanceStuck of string

  val replay_error_text : exn -> string
  val trusted : Thm.thm -> bool
  val conform_conclusion : string -> term -> Thm.thm -> Thm.thm
  val eval : term -> Thm.thm
  val eval_original : term -> Thm.thm
  val head_name : term -> string
  val equality_portfolio :
    int -> (string -> term -> (term -> Thm.thm) -> Thm.thm option) -> term ->
    Thm.thm option
  val is_quantifier : term -> bool
  val evaluate_instance :
    int -> (string -> term -> (term -> Thm.thm) -> Thm.thm option) -> term ->
    instance_verdict
  val eval_term : (term * term) list -> term -> term
  val closure_of : term -> term list * term * term
  val refute_forall : term -> term list -> Thm.thm -> Thm.thm
  val refute_exists : string -> term -> term -> Thm.thm -> Thm.thm
  val normalize_to_pnf :
    (Abbrev.conv -> term -> Thm.thm) -> term -> Thm.thm * Thm.thm * term
  val undo_normalization : string -> Thm.thm * Thm.thm -> Thm.thm -> Thm.thm
  val constructor_resolver : unit -> Type.hol_type -> term list option
  val replace :
    Refute_Core.counterexample -> Refute_Core.certainty ->
    (term * term) list -> Thm.thm option -> Refute_Core.counterexample
  val certify :
    {cex : Refute_Core.counterexample,
     env : (term * term) list,
     evals : term list,
     original : term} ->
    result
  val ground_and_certify :
    {cex : Refute_Core.counterexample,
     env : (term * term) list,
     evals : term list,
     ground_env : (term * term) list option,
     original : term} ->
    result
end
