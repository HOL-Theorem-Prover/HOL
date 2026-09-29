signature Refute_Core = sig
  type term = Term.term
  type thm = Thm.thm
  type hol_type = Type.hol_type

  (* The result of [ThmSetData.export_list]. *)
  type theorem_set =
    {merge : string list -> thm list option,
     DB : {thyname : string} -> thm list option,
     export : string -> unit,
     temp_export : string -> unit,
     temp_exclude : thm -> unit,
     getDB : unit -> thm list,
     temp_setDB : thm list -> unit}

  val refute_simp : theorem_set
  val refute_psimp : theorem_set
  val refute_unfold : theorem_set

  datatype certainty =
      Genuine
    | QuasiGenuine of string list
    | Potential of string list

  type model_report =
    { skolems : (string * term) list,
      consts : (term * string * term) list,
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

  datatype outcome =
      Counterexample of counterexample list
    | NoCounterexample
    | Model of counterexample list
    | NoModel
    | Unknown of string list

  type problem =
    { goal : term,
      assumptions : term list,
      evals : term list }

  datatype expectation =
      NoExpectation
    | ExpectNone
    | ExpectUnknown
    | ExpectCex
    | ExpectModel
    | ExpectNoModel
    | ExpectGenuine
    | ExpectQuasiGenuine
    | ExpectPotential

  datatype substrate_choice = Auto | Compute | NativeSML

  datatype bound_mode = FixedBound | IterativeDeepening

  type qc_config =
    { size : int,
      size_mode : bound_mode,
      iterations : int,
      depth : int,
      finite_types : bool,
      finite_type_size : int,
      default_type : hol_type list,
      substrate : substrate_choice,
      seed : int option,
      allow_existentials : bool,
      finite_functions : bool,
      certify : bool,
      smart_quantifier : bool,
      smart_generators : bool,
      optimise_equality : bool,
      reorder_premises : bool,
      (* Function inversion: synthesise Horn clauses for a function's
         graph from its defining equations and run mode inference over
         them, so a premise recognising [f a b = z] drives an inverting
         generator ([Refute_QC]'s [graph_recognise] and
         [graph_positive_candidates]).  Off by default, matching Isabelle
         Quickcheck's [quickcheck_allow_function_inversion] flag: an
         under-approximating graph used as a generator is unsound. *)
      allow_function_inversion : bool,
      (* Per-type-variable pins for QC's monomorphizing substitution.  A
         [SOME tyvar] key pins that variable; [NONE] is the fallback for
         every non-width variable no [SOME] entry names.  A width type
         variable (a word's index) takes a pin only from its own [SOME]
         entry -- [NONE] never reaches it, because carriers and fcp-numeral
         widths are disjoint value spaces and a single fallback value
         cannot serve both.  A variable no entry reaches keeps taking the
         single carrier/width [monomorphic_types] indexes by instance,
         exactly as when this list is []. *)
      instantiate : (hol_type option * hol_type) list,
      (* Rep->abs transport for a variable at a typedef type with no
         generator: see [Refute_QC]'s [transport_instance], installed
         through [register_mono_instance_transform] below.  Off by
         default, matching the default of Isabelle's [use_subtype] flag;
         the transform itself is the dual of Isabelle's, which rewrites a
         representation-typed variable constrained by a registered subtype
         predicate into [Rep] of an abstract-typed one. *)
      use_subtype : bool }

  type mf_config =
    { card : (hol_type option * int list) list,
      card_mode : bound_mode,
      max : (term option * int list) list,
      mono : (hol_type option * bool option) list,
      wf : (term option * bool option) list,
      sat_solver : string,
      batch_size : int,
      falsify : bool,
      user_axioms : bool option,
      destroy_constrs : bool,
      total_consts : bool option,
      peephole_optim : bool,
      datatype_sym_break : int,
      kodkod_sym_break : int,
      max_potential : int,
      max_genuine : int,
      atoms : (hol_type option * string list) list,
      format : (term option * int list) list,
      show_types : bool,
      show_skolems : bool,
      show_consts : bool,
      debug : bool,
      overlord : bool,
      max_threads : int,
      tac_timeout : real,
      specialize : bool,
      box : (hol_type option * bool option) list,
      binary_ints : bool option,
      bits : int list,
      star_linear_preds : bool,
      iter : (term option * int list) list,
      bisim_depth : int list,
      finitize : (hol_type option * bool option) list,
      whack : term list,
      need : term list option,
      merge_type_vars : bool }

  type config =
    { timeout : real,
      backends : string list option,
      sequential : bool,
      genuine_only : bool,
      abort_potential : bool,
      quiet : bool,
      no_assms : bool,
      evals : term list,
      expect : expectation,
      max_counterexamples : int,
      tag : string,
      (* Machine-word widths substituted for a type variable in a word's
         index position.  Unrelated to [mf.bits], which sizes binary
         integers. *)
      widths : int list,
      qc : qc_config,
      mf : mf_config }

  type instance =
    { original : term,
      goal : term,
      qc_gate : string list option,
      evals : term list,
      card : int,
      size_matters : bool,
      (* [use_subtype] rep->abs transport record, [(r, x, abs)]: [r]
         is the representation-typed variable [goal] now carries in
         place of the user's [x], and [abs] rebuilds [x]'s reported
         value from a candidate binding for [r].  Empty unless
         [Refute_QC]'s transform fired on this instance. *)
      transport : (term * term * term) list }

  datatype requirement =
      AnyGoal
    | ExecutableGoal
    | ExecutableGoalUnless of config -> instance list -> bool

  datatype goal_form = MonoInstances | PolyOriginal

  type certainty_ceiling = config -> instance list -> certainty

  type backend =
    { name : string,
      weight : int,
      configured : unit -> bool,
      requires : requirement,
      input : goal_form,
      certainty_ceiling : certainty_ceiling,
      run : config -> instance list -> outcome }

  val default_qc_config : qc_config
  val default_mf_config : mf_config
  val default_config : config
  val config_of : Context.t -> config
  val set_config : config -> unit
  val with_config : config -> ('a -> 'b) -> 'a -> 'b
  val upd_timeout : real -> config -> config
  val upd_backends : string list option -> config -> config
  val upd_sequential : bool -> config -> config
  val upd_genuine_only : bool -> config -> config
  val upd_abort_potential : bool -> config -> config
  val upd_quiet : bool -> config -> config
  val upd_no_assms : bool -> config -> config
  val upd_evals : term list -> config -> config
  val upd_expect : expectation -> config -> config
  val upd_max_counterexamples : int -> config -> config
  val upd_tag : string -> config -> config
  val upd_widths : int list -> config -> config
  val upd_qc : qc_config -> config -> config
  val upd_size : int -> config -> config
  val upd_iterative_size : int -> config -> config
  val upd_iterations : int -> config -> config
  val upd_depth : int -> config -> config
  val upd_finite_types : bool -> config -> config
  val upd_finite_type_size : int -> config -> config
  val upd_default_type : hol_type list -> config -> config
  val upd_substrate : substrate_choice -> config -> config
  val upd_seed : int option -> config -> config
  val upd_allow_existentials : bool -> config -> config
  val upd_finite_functions : bool -> config -> config
  val upd_certify : bool -> config -> config
  val upd_smart_quantifier : bool -> config -> config
  val upd_smart_generators : bool -> config -> config
  val upd_optimise_equality : bool -> config -> config
  val upd_reorder_premises : bool -> config -> config
  val upd_instantiate : (hol_type option * hol_type) list -> config -> config
  val upd_use_subtype : bool -> config -> config
  val upd_allow_function_inversion : bool -> config -> config

  datatype mf_update =
      MfCard of (hol_type option * int list) list * bound_mode
    | MfMax of (term option * int list) list
    | MfMono of (hol_type option * bool option) list
    | MfWf of (term option * bool option) list
    | MfSatSolver of string
    | MfBatchSize of int
    | MfFalsify of bool
    | MfUserAxioms of bool option
    | MfDestroyConstrs of bool
    | MfTotalConsts of bool option
    | MfPeepholeOptim of bool
    | MfDatatypeSymBreak of int
    | MfKodkodSymBreak of int
    | MfMaxPotential of int
    | MfMaxGenuine of int
    | MfAtoms of (hol_type option * string list) list
    | MfFormat of (term option * int list) list
    | MfShowTypes of bool
    | MfShowSkolems of bool
    | MfShowConsts of bool
    | MfDebug of bool
    | MfOverlord of bool
    | MfMaxThreads of int
    | MfTacTimeout of real
    | MfSpecialize of bool
    | MfBox of (hol_type option * bool option) list
    | MfBinaryInts of bool option
    | MfBits of int list
    | MfStarLinearPreds of bool
    | MfIter of (term option * int list) list
    | MfBisimDepth of int list
    | MfFinitize of (hol_type option * bool option) list
    | MfWhack of term list
    | MfNeed of term list option
    | MfMergeTypeVars of bool

  val change_mf : mf_update -> mf_config -> mf_config
  val upd_mf : mf_config -> config -> config
  val upd_card : (hol_type option * int list) list -> config -> config
  val upd_iterative_card :
    (hol_type option * int list) list -> config -> config
  val upd_max : (term option * int list) list -> config -> config
  val upd_mono : (hol_type option * bool option) list -> config -> config
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
  val upd_atoms : (hol_type option * string list) list -> config -> config
  val upd_format : (term option * int list) list -> config -> config
  val upd_show_types : bool -> config -> config
  val upd_show_skolems : bool -> config -> config
  val upd_show_consts : bool -> config -> config
  val upd_debug : bool -> config -> config
  val upd_overlord : bool -> config -> config
  val upd_max_threads : int -> config -> config
  val upd_tac_timeout : real -> config -> config
  val upd_specialize : bool -> config -> config
  val upd_box : (hol_type option * bool option) list -> config -> config
  val upd_binary_ints : bool option -> config -> config
  val upd_bits : int list -> config -> config
  val upd_star_linear_preds : bool -> config -> config
  val upd_iter : (term option * int list) list -> config -> config
  val upd_bisim_depth : int list -> config -> config
  val upd_finitize : (hol_type option * bool option) list -> config -> config
  val upd_whack : term list -> config -> config
  val upd_need : term list option -> config -> config
  val upd_merge_type_vars : bool -> config -> config
  val bounded_rewrites : thm list
  val normal_rewrites : thm list
  val has_bounded_quantifier : term -> bool
  val normalize : term -> term
  val has_unexpanded_binder : term -> bool
  val nonexecutable_constants : term list -> term list
  val show_constants : term list -> string
  val rebuild_instance :
    {original : term, raw_goal : term, evals_for : term -> term list,
     card : int, transport : (term * term * term) list} -> instance
  val register_mono_instance_transform :
    (config -> instance -> instance) -> unit
  val show_config : unit -> unit
  val register_run_release : string -> (unit -> unit) -> unit
  val register_backend : backend -> unit
  val lookup_stat : ''a -> (''a * 'b) list -> 'b option
  val format_scope_assignment : hol_type * int -> string
  val report_outcome : config -> outcome -> unit

  type search_context =
    { started : Time.time,
      deadline : Time.time,
      expired : unit -> bool,
      remaining : unit -> Time.time }

  val publish_counterexamples : counterexample list -> unit
  val publish_models : counterexample list -> unit
  val search_context_for : config -> search_context
  val with_search_context : config -> ('a -> 'b) -> 'a -> 'b
  val search_expired : config -> bool
  val add_reason : ''a * ''a list -> ''a list
  val instance_is_executable : instance -> bool
  val refute_problem : Context.t -> config -> problem -> outcome
  val refute : Context.t -> config -> term -> outcome
  (* Output shared by every backend worker: [say] and [warn] serialize
     whole messages, [enabled] tests the "Refute" trace level. *)
  structure Private : sig
    val enabled : int -> bool
    val say : int -> string -> unit
    val warn : string -> string -> string -> unit
  end
end
