signature Refute_Config = sig
  (* Configuration shared by [Refute_Core] and the [Refute] facade,
     which replaces [Refute_Core.upd_backends] with [upd_search]. *)

  (* [ExpectNone] matches only [NoCounterexample];
     [ExpectUnknown] is the appropriate pin for a bounds-relative miss.
     [ExpectModel] and [ExpectNoModel] pin model-search outcomes. *)
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
      default_type : Type.hol_type list,
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
      instantiate : (Type.hol_type option * Type.hol_type) list,
      (* Rep->abs transport for a variable at a typedef type with no
         generator: see [Refute_QC]'s [transport_instance], installed
         through [Refute_Core.register_mono_instance_transform].  Off by
         default, matching the default of Isabelle's [use_subtype] flag;
         the transform itself is the dual of Isabelle's, which rewrites a
         representation-typed variable constrained by a registered subtype
         predicate into [Rep] of an abstract-typed one. *)
      use_subtype : bool }

  type mf_config =
    { card : (Type.hol_type option * int list) list,
      card_mode : bound_mode,
      max : (Term.term option * int list) list,
      mono : (Type.hol_type option * bool option) list,
      wf : (Term.term option * bool option) list,
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
      atoms : (Type.hol_type option * string list) list,
      format : (Term.term option * int list) list,
      show_types : bool,
      show_skolems : bool,
      show_consts : bool,
      debug : bool,
      overlord : bool,
      max_threads : int,
      tac_timeout : real,
      specialize : bool,
      box : (Type.hol_type option * bool option) list,
      binary_ints : bool option,
      bits : int list,
      star_linear_preds : bool,
      iter : (Term.term option * int list) list,
      bisim_depth : int list,
      finitize : (Type.hol_type option * bool option) list,
      whack : Term.term list,
      need : Term.term list option,
      merge_type_vars : bool }

  type config =
    { timeout : real,
      backends : string list option,
      sequential : bool,
      genuine_only : bool,
      abort_potential : bool,
      quiet : bool,
      no_assms : bool,
      evals : Term.term list,
      expect : expectation,
      max_counterexamples : int,
      tag : string,
      (* Machine-word widths substituted for a type variable in a word's
         index position.  Unrelated to [mf.bits], which sizes binary
         integers. *)
      widths : int list,
      qc : qc_config,
      mf : mf_config }

  val default_qc_config : qc_config
  val default_mf_config : mf_config
  val default_config : config
  (* The stored configuration lives in the context: [set_config]
     replaces it and [with_config] installs one for the duration of a
     call. *)
  val set_config : config -> unit
  val with_config : config -> ('a -> 'b) -> 'a -> 'b
  val upd_timeout : real -> config -> config
  val upd_sequential : bool -> config -> config
  val upd_genuine_only : bool -> config -> config
  val upd_abort_potential : bool -> config -> config
  val upd_quiet : bool -> config -> config
  val upd_no_assms : bool -> config -> config
  val upd_evals : Term.term list -> config -> config
  val upd_expect : expectation -> config -> config
  val upd_max_counterexamples : int -> config -> config
  val upd_tag : string -> config -> config
  val upd_qc : qc_config -> config -> config
  val upd_size : int -> config -> config
  val upd_iterative_size : int -> config -> config
  val upd_iterations : int -> config -> config
  val upd_depth : int -> config -> config
  val upd_finite_types : bool -> config -> config
  val upd_finite_type_size : int -> config -> config
  (* Word widths tried for a type variable in a word's index position;
     [upd_bits] is the unrelated binary-integer width. *)
  val upd_widths : int list -> config -> config
  val upd_default_type : Type.hol_type list -> config -> config
  (* Per-type-variable QC instantiation pins; [NONE] is the fallback for
     every non-width variable no [SOME] entry names -- a width variable
     (a word's index) takes a pin only from its own [SOME] entry.  An
     unpinned variable keeps taking the single indexed carrier/width,
     exactly as with []. *)
  val upd_instantiate :
    (Type.hol_type option * Type.hol_type) list -> config -> config
  (* Rep->abs transport: a free variable at a typedef type with no
     generator of its own is replaced by [abs r] for a fresh
     representation-typed [r], guarded by the characteristic predicate
     applied to [r].  Off by default, matching Isabelle's [use_subtype];
     never applied to the model finder's input, which handles typedefs
     natively; does not reach an occurrence nested inside another type
     (e.g. a free variable of type [t list] is untouched). *)
  val upd_use_subtype : bool -> config -> config
  val upd_substrate : substrate_choice -> config -> config
  val upd_seed : int option -> config -> config
  val upd_allow_existentials : bool -> config -> config
  val upd_finite_functions : bool -> config -> config
  val upd_certify : bool -> config -> config
  val upd_smart_quantifier : bool -> config -> config
  val upd_smart_generators : bool -> config -> config
  val upd_optimise_equality : bool -> config -> config
  val upd_reorder_premises : bool -> config -> config
  (* Function inversion (synthesise a function's graph clauses from its
     defining equations and run mode inference over them, see
     [Refute_SmartGen.infer_graph]) names Isabelle Quickcheck's own
     function-inversion flag, off by default.  When set, a goal premise
     recognising [f a1 ... an = res] -- [f] a constant applied at exactly
     its own maximal arity, every position either fully bound or a bare
     unbound variable -- may compile to an [Enum] that inverts [f]'s
     graph instead of an opaque guard, competing on score with every
     other route exactly as an ordinary relational premise does.  Also
     needs [upd_smart_generators] (default on): this is itself a
     smart-generator route, so turning that off disables it too. *)
  val upd_allow_function_inversion : bool -> config -> config
  val upd_mf : mf_config -> config -> config
  val upd_card : (Type.hol_type option * int list) list -> config -> config
  val upd_iterative_card :
    (Type.hol_type option * int list) list -> config -> config
  val upd_max : (Term.term option * int list) list -> config -> config
  val upd_mono :
    (Type.hol_type option * bool option) list -> config -> config
  val upd_wf : (Term.term option * bool option) list -> config -> config
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
    (Type.hol_type option * string list) list -> config -> config
  val upd_format : (Term.term option * int list) list -> config -> config
  val upd_show_types : bool -> config -> config
  val upd_show_skolems : bool -> config -> config
  val upd_show_consts : bool -> config -> config
  val upd_debug : bool -> config -> config
  val upd_overlord : bool -> config -> config
  val upd_max_threads : int -> config -> config
  val upd_tac_timeout : real -> config -> config
  val upd_specialize : bool -> config -> config
  val upd_box :
    (Type.hol_type option * bool option) list -> config -> config
  val upd_binary_ints : bool option -> config -> config
  val upd_bits : int list -> config -> config
  val upd_star_linear_preds : bool -> config -> config
  (* A mutual fixpoint group shares one iterator row.  Group members are
     checked in cases-theorem order, and the first explicit row wins. *)
  val upd_iter : (Term.term option * int list) list -> config -> config
  val upd_bisim_depth : int list -> config -> config
  val upd_finitize :
    (Type.hol_type option * bool option) list -> config -> config
  val upd_whack : Term.term list -> config -> config
  val upd_need : Term.term list option -> config -> config
  val upd_merge_type_vars : bool -> config -> config
end
