signature Refute = sig
  type term = Term.term
  type thm = Thm.thm
  type hol_type = Type.hol_type
  type goal = term list * term

  datatype certainty = Genuine | QuasiGenuine of string list
                     | Potential of string list
  type counterexample =
    { backend : string,
      substrate : string,
      certainty : certainty,
      bindings : (term * term) list,
      evals : (term * term) list,
      cert : thm option,
      scope : (hol_type * int) list option,
      stats : (string * int) list }
  datatype outcome = Counterexample of counterexample list
                   | NoCounterexample
                   | Unknown of string list
  datatype expectation = NoExpectation | ExpectNone | ExpectUnknown
                       | ExpectCex | ExpectGenuine | ExpectQuasiGenuine
                       | ExpectPotential
  datatype substrate_choice = Auto | Compute | Cv | NativeSML
  datatype requirement = datatype Refute_Core.requirement
  type qc_config = Refute_Core.qc_config
  type config = Refute_Core.config
  type backend = Refute_Core.backend
  type substrate = Refute_Eval.substrate
  type custom_gen = Refute_Gen.custom_gen
  type rng = Refute_Gen.rng

  val refute        : config -> term -> outcome
  val refute_def    : term -> outcome
  val refute_goal   : config -> goal -> outcome
  val refute_top    : unit -> outcome
  val quickcheck    : term -> outcome
  val REFUTE_TAC    : Abbrev.tactic

  val register_backend : backend -> unit
  val register_substrate : substrate -> unit
  val register_generator : hol_type -> custom_gen -> unit
  val abstract_generator :
    {ty : hol_type, constructors : term list, pred : term option} -> unit
  val export_refute_simp : string -> unit
  val export_refute_psimp : string -> unit
  val export_refute_unfold : string -> unit

  val default_qc_config : qc_config
  val default_config : config
  val the_config : config ref
  val show_config : unit -> unit
  val upd_timeout : real -> config -> config
  val upd_backends : string list option -> config -> config
  val upd_sequential : bool -> config -> config
  val upd_genuine_only : bool -> config -> config
  val upd_abort_potential : bool -> config -> config
  val upd_no_assms : bool -> config -> config
  val upd_evals : term list -> config -> config
  val upd_expect : expectation -> config -> config
  val upd_max_counterexamples : int -> config -> config
  val upd_tag : string -> config -> config
  val upd_qc : qc_config -> config -> config
  val upd_size : int -> config -> config
  val upd_iterations : int -> config -> config
  val upd_depth : int -> config -> config
  val upd_finite_types : bool -> config -> config
  val upd_finite_type_size : int -> config -> config
  val upd_default_type : hol_type list -> config -> config
  val upd_substrate : substrate_choice -> config -> config
  val upd_allow_function_inversion : bool -> config -> config
  val upd_use_subtype : bool -> config -> config
  val upd_seed : int option -> config -> config
  val upd_smart_quantifier : bool -> config -> config
  val upd_optimise_equality : bool -> config -> config
end
