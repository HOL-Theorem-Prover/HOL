signature Refute = sig
  type term = Term.term
  type thm = Thm.thm
  type hol_type = Type.hol_type
  type goal = term list * term

  datatype certainty = Genuine | QuasiGenuine of string list
                     | Potential of string list
  type model_report =
    { skolems : (string * term) list,
      consts : (term * term) list,
      types : (hol_type * term list * bool) list }
  type counterexample =
    { backend : string,
      substrate : string,
      certainty : certainty,
      bindings : (term * term) list,
      evals : (term * term) list,
      cert : thm option,
      scope : (hol_type * int) list option,
      model : model_report option,
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
  type mf_config = Refute_Core.mf_config
  type config = Refute_Core.config
  type instance = Refute_Core.instance
  type backend = Refute_Core.backend
  type certainty_ceiling = config -> instance list -> certainty
  type substrate = Refute_Eval.substrate
  type custom_gen = Refute_Gen.custom_gen
  type rng = Refute_Gen.rng

  val refute        : config -> term -> outcome
  val refute_def    : term -> outcome
  val refute_goal   : config -> goal -> outcome
  val refute_top    : unit -> outcome
  val quickcheck    : term -> outcome
  val nitpick       : term -> outcome
  val REFUTE_TAC    : Abbrev.tactic

  val register_backend : backend -> unit
  (* The callback must upper-bound the certainty returned by the backend's
     [run] function for the same configuration and instances. *)
  val register_backend_with_ceiling :
    backend -> certainty_ceiling -> unit
  val register_substrate : substrate -> unit
  val register_generator : hol_type -> custom_gen -> unit
  val abstract_generator :
    {ty : hol_type, constructors : term list, pred : term option} -> unit
  val export_refute_simp : string -> unit
  val export_refute_psimp : string -> unit
  val export_refute_unfold : string -> unit

  val default_qc_config : qc_config
  val default_mf_config : mf_config
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
  val upd_mf : mf_config -> config -> config
  val upd_card : (hol_type option * int list) list -> config -> config
  val upd_max : (term option * int list) list -> config -> config
  val upd_mono :
    (hol_type option * bool option) list -> config -> config
  val upd_wf : (term option * bool option) list -> config -> config
  val upd_sat_solver : string -> config -> config
  val upd_batch_size : int -> config -> config
  val upd_falsify : bool -> config -> config
  val upd_user_axioms : bool option -> config -> config
  val upd_destroy_constrs : bool -> config -> config
  val upd_total_consts : bool option -> config -> config
  val upd_peephole_optim : bool -> config -> config
  val upd_datatype_sym_break : int -> config -> config
  val upd_kodkod_sym_break : int -> config -> config
  val upd_max_potential : int -> config -> config
  val upd_max_genuine : int -> config -> config
  val upd_atoms :
    (hol_type option * string list) list -> config -> config
  val upd_format : (term option * int list) list -> config -> config
  val upd_show_types : bool -> config -> config
  val upd_show_skolems : bool -> config -> config
  val upd_show_consts : bool -> config -> config
  val upd_debug : bool -> config -> config
  val upd_overlord : bool -> config -> config
  val upd_max_threads : int -> config -> config
  val upd_tac_timeout : real -> config -> config
  val upd_specialize : bool -> config -> config
  val upd_box :
    (hol_type option * bool option) list -> config -> config
  val upd_binary_ints : bool option -> config -> config
  val upd_bits : int list -> config -> config
  val upd_star_linear_preds : bool -> config -> config
  val upd_iter : (term option * int list) list -> config -> config
  val upd_bisim_depth : int list -> config -> config
  val upd_finitize :
    (hol_type option * bool option) list -> config -> config
  val upd_whack : term list -> config -> config
  val upd_need : term list option -> config -> config
end
