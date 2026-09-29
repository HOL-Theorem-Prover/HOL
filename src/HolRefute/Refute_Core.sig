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

  include Refute_Config

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

  datatype backend_family = QuickcheckFamily | ModelFinderFamily | OtherFamily

  (* A witness's backend-specific text, each part empty or starting with a
     newline: the scope, the bindings, and the model after the evaluated
     terms. *)
  type witness_text = {scope : string, bindings : string, model : string}

  type backend =
    { name : string,
      family : backend_family,
      weight : int,
      configured : unit -> bool,
      requires : requirement,
      input : goal_form,
      certainty_ceiling : certainty_ceiling,
      run : config -> instance list -> outcome,
      (* [NONE] shows the bindings with [format_term]. *)
      render : (mf_config -> counterexample -> witness_text) option }

  val config_of : Context.t -> config
  val upd_backends : string list option -> config -> config

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
  val family_backend_names : backend_family -> string list
  val lookup_stat : ''a -> (''a * 'b) list -> 'b option
  (* One QC substrate call's candidate counters; the stats list is only
     their rendering. *)
  type qc_counters = {generated : int, satisfied : int, evaluated : int}
  val no_counters : qc_counters
  val add_counters : qc_counters -> qc_counters -> qc_counters
  val counter_stats : qc_counters -> (string * int) list
  val counters_of_stats : (string * int) list -> qc_counters option
  val is_counter_stat : string -> bool
  val substrate_stats :
    {tests : int, match_failures : int, counters : qc_counters} ->
    (string * int) list
  val format_counters : qc_counters -> string
  val format_term : term -> string
  val format_pairs : (term -> string) -> (term * term) list -> string
  val boolean_value_for_display : term -> term option
  val type_name : hol_type -> string
  val report_outcome : config -> outcome -> unit

  type search_context =
    { started : Time.time,
      deadline : Time.time,
      expired : unit -> bool,
      remaining : unit -> Time.time,
      memo : Universal.universal list Synchronized.var }

  (* [call_memo key build] runs [build] once per key for the running
     Refute call, backends included; outside a call it just runs it. *)
  type 'a call_key
  val call_key : unit -> 'a call_key
  val call_memo : 'a call_key -> (unit -> 'a) -> 'a

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
