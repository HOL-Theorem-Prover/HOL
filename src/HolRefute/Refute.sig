signature Refute = sig
  type term = Term.term
  type thm = Thm.thm
  type hol_type = Type.hol_type
  type goal = term list * term

  datatype certainty = datatype Refute_Core.certainty
  type model_report = Refute_Core.model_report
  type counterexample = Refute_Core.counterexample
  (* [NoCounterexample] says that the whole relevant space was covered and
     no counterexample is possible.  A clean search limited to non-covering
     bounds is [Unknown] and includes its frontier in the reasons.
     [Model] and [NoModel] are the distinct results of Kodkod model search;
     backend choice never changes the meaning of another constructor. *)
  datatype outcome = datatype Refute_Core.outcome
  (* [ExpectNone] matches only the whole-space outcome above;
     [ExpectUnknown] is the appropriate pin for a bounds-relative miss.
     [ExpectModel] and [ExpectNoModel] pin model-search outcomes. *)
  datatype expectation = datatype Refute_Core.expectation
  datatype substrate_choice = datatype Refute_Core.substrate_choice
  datatype bound_mode = datatype Refute_Core.bound_mode
  datatype requirement = datatype Refute_Core.requirement
  datatype goal_form = datatype Refute_Core.goal_form
  type qc_config = Refute_Core.qc_config
  type mf_config = Refute_Core.mf_config
  type config = Refute_Core.config
  type instance = Refute_Core.instance
  type backend = Refute_Core.backend
  type custom_gen = Refute_Gen.custom_gen
  type rng = Refute_Gen.rng
  type term_postprocessor = term -> term

  datatype backend_choice =
      Exhaustive
    | Random
    | Narrowing
    | ModelFinder
    | RegisteredBackend of string

  datatype search =
      AllBackends
    | QuickcheckBackends
    | Only of backend_choice list

  type config_update = config -> config

  val refute        : config -> term -> outcome
  val refute_def    : term -> outcome
  val refute_with   : config_update list -> term -> outcome
  val refute_goal   : config -> goal -> outcome
  val refute_goal_with : config_update list -> goal -> outcome
  val refute_top    : unit -> outcome
  val try_refute    : config -> goal -> (string * outcome) option
  (* [NONE] derives a QC-only configuration from [the_config].  [SOME cfg]
     supplies the base configuration and preserves its backend selection.
     Every probe forces a sequential, quiet, abort-potential,
     expectation-free profile. *)
  val check_unused_assms :
    config option -> string * thm -> string * int list list option
  val find_unused_assms :
    config option -> string -> (string * int list list option) list
  val print_unused_assms : config option -> string option -> unit
  val quickcheck    : term -> outcome
  val model_refute  : term -> outcome
  (* Diagnostic tactics return the original goal unchanged.  The exact-config
     form honours every field.  The update form reads [the_config] when the
     tactic is applied, then applies its updates from left to right. *)
  val REFUTE_CONFIG_TAC : config -> Abbrev.tactic
  val REFUTE_TAC_WITH   : config_update list -> Abbrev.tactic
  val REFUTE_TAC        : Abbrev.tactic
  val QUICKCHECK_TAC    : Abbrev.tactic
  val NARROWING_TAC     : Abbrev.tactic
  val MODEL_REFUTE_TAC  : Abbrev.tactic

  val register_backend : backend -> unit
  val register_generator : hol_type -> custom_gen -> unit
  (* Registers a QC generator for every concrete instance of a type
     operator, built from constructor constants whose declared result type
     is [tyop] applied to distinct type variables (e.g. FEMPTY/FUPDATE for
     [:'a |-> 'b]).  Unlike [register_generator], nothing is stored per
     instance: [tyop] is matched on demand, so this fires for a type never
     previously seen.  The resulting generator always has
     [exhaustive = false].  [canonical], if present, rewrites a generated
     candidate for display by removing structure that a later part of the
     same candidate has overwritten; it never affects the term used for
     testing or certification, and need not identify every pair of terms
     that denote the same value. *)
  val register_generator_family :
    {tyop : {Thy : string, Tyop : string}, constructors : term list,
     canonical : term_postprocessor option} -> unit
  val register_term_postprocessor :
    hol_type -> term_postprocessor -> unit
  (* [witness = SOME thm] rules out generic shape defeats: [thm] must be
     [?x. x = C ... x ...] for a registered constructor [C], showing some
     value is cyclic.  For a type the datatype database already knows,
     the constructor list is separately cross-checked against it; beyond
     that it remains the caller's assertion.  See [README] for the exact
     shape. *)
  val register_codatatype :
    {tyop : {Thy : string, Tyop : string},
     case_const : term, constructors : term list, witness : thm option} ->
    unit
  val register_quotient :
    {qty : hol_type, rty : hol_type, abs : term, rep : term,
     equiv_thm : thm} -> unit
  val register_typedef :
    {ty : hol_type, abs : term, rep : term, absrep_thms : thm list} -> unit
  (* Sweeps every theory in [Theory.ancestry] once, in a canonical
     deterministic order, attempting typedef and quotient harvesting for
     every type operator those theories declare.  The lazy, demand-driven
     harvest remains the default; this is an opt-in alternative for a
     caller who would rather pay the scan upfront.  Returns only what this
     call newly registered - a type already registered, explicitly or by
     an earlier harvest, is not listed - so an immediate second call
     returns empty lists.  [theories_scanned] is this whole ancestry, not
     the (much narrower, per-operator) set of theories whose theorems were
     actually inspected. *)
  val harvest_registrations : unit ->
    {typedefs : hol_type list, quotients : hol_type list,
     theories_scanned : string list}
  val register_frac_type :
    {tyop : {Thy : string, Tyop : string},
     ersatz :
       {original : {Thy : string, Name : string},
        replacement : {Thy : string, Name : string}} list} -> unit
  val register_ersatz :
    {original : {Thy : string, Name : string},
     replacement : {Thy : string, Name : string}} -> unit
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
  val upd_search : search -> config_update
  val apply_updates : config_update list -> config -> config
  val current_config : config_update list -> config
  val upd_timeout : real -> config -> config
  val upd_sequential : bool -> config -> config
  val upd_genuine_only : bool -> config -> config
  val upd_abort_potential : bool -> config -> config
  val upd_quiet : bool -> config -> config
  val upd_no_assms : bool -> config -> config
  val upd_evals : term list -> config -> config
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
  val upd_default_type : hol_type list -> config -> config
  (* Per-type-variable QC instantiation pins; [NONE] is the fallback for
     every non-width variable no [SOME] entry names -- a width variable
     (a word's index) takes a pin only from its own [SOME] entry.  An
     unpinned variable keeps taking the single indexed carrier/width,
     exactly as with []. *)
  val upd_instantiate :
    (hol_type option * hol_type) list -> config -> config
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
  val upd_card : (hol_type option * int list) list -> config -> config
  val upd_iterative_card :
    (hol_type option * int list) list -> config -> config
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
  (* A mutual fixpoint group shares one iterator row.  Group members are
     checked in cases-theorem order, and the first explicit row wins. *)
  val upd_iter : (term option * int list) list -> config -> config
  val upd_bisim_depth : int list -> config -> config
  val upd_finitize :
    (hol_type option * bool option) list -> config -> config
  val upd_whack : term list -> config -> config
  val upd_need : term list option -> config -> config
  val upd_merge_type_vars : bool -> config -> config
end
