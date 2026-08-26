structure Refute_Core = struct
  structure Names = Refute_ModelFinder_Names

  type term = Term.term
  type thm = Thm.thm
  type hol_type = Type.hol_type

  val refute_simp =
    ThmSetData.export_list {settype = "refute_simp", initial = []}

  val refute_psimp =
    ThmSetData.export_list {settype = "refute_psimp", initial = []}

  val refute_unfold =
    ThmSetData.export_list {settype = "refute_unfold", initial = []}

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

  datatype substrate_choice = Auto | Compute | Cv | NativeSML

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
         them, so a premise recognising [f a b = z] could drive an
         inverting generator.  Off by default, matching Isabelle
         Quickcheck's own function-inversion flag: an under-approximating
         graph used as a generator is unsound, and no goal-premise
         recogniser consumes this yet. *)
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
         default, matching Isabelle's [use_subtype]. *)
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

  type backend =
    { name : string,
      weight : int,
      configured : unit -> bool,
      requires : requirement,
      input : goal_form,
      run : config -> instance list -> outcome }

  (* A ceiling must overestimate the best certainty [run] can return for
     the same configuration and instances.  Overestimates only miss an
     early stop; underestimates can suppress a stronger backend result. *)
  type certainty_ceiling = config -> instance list -> certainty

  type backend_registration =
    { backend : backend,
      certainty_ceiling : certainty_ceiling }

  val default_qc_config : qc_config =
    { size = 10,
      size_mode = IterativeDeepening,
      iterations = 100,
      depth = 10,
      finite_types = true,
      finite_type_size = 3,
      default_type = [``:num``],
      substrate = Auto,
      seed = NONE,
      allow_existentials = true,
      finite_functions = true,
      certify = true,
      smart_quantifier = true,
      smart_generators = true,
      optimise_equality = true,
      reorder_premises = true,
      instantiate = [],
      use_subtype = false,
      allow_function_inversion = false }

  val default_mf_config : mf_config =
    { card = [(NONE, List.tabulate (10, fn n => n + 1))],
      card_mode = IterativeDeepening,
      max = [(NONE, [~1])],
      mono = [(NONE, NONE)],
      wf = [(NONE, NONE)],
      sat_solver = "smart",
      batch_size = 50,
      falsify = true,
      user_axioms = NONE,
      destroy_constrs = true,
      total_consts = NONE,
      peephole_optim = true,
      datatype_sym_break = 5,
      kodkod_sym_break = 15,
      max_potential = 1,
      max_genuine = 1,
      atoms = [(NONE, [])],
      format = [(NONE, [1])],
      show_types = false,
      show_skolems = true,
      show_consts = false,
      debug = false,
      overlord = false,
      max_threads = 0,
      tac_timeout = 0.5,
      specialize = true,
      box = [(NONE, NONE)],
      binary_ints = NONE,
      bits = List.tabulate (10, fn n => n + 1),
      star_linear_preds = true,
      iter = [(NONE, [0, 1, 2, 4, 8, 12, 16, 20, 24, 28])],
      bisim_depth = [9],
      finitize = [(NONE, NONE)],
      whack = [],
      need = NONE,
      merge_type_vars = false }

  val default_config : config =
    { timeout = 10.0,
      backends = NONE,
      sequential = false,
      genuine_only = false,
      abort_potential = false,
      quiet = false,
      no_assms = false,
      evals = [],
      expect = NoExpectation,
      max_counterexamples = 1,
      tag = "",
      widths = [1, 2, 3, 4],
      qc = default_qc_config,
      mf = default_mf_config }

  val the_config = ref default_config

  datatype config_update =
      ConfigTimeout of real
    | ConfigBackends of string list option
    | ConfigSequential of bool
    | ConfigGenuineOnly of bool
    | ConfigAbortPotential of bool
    | ConfigQuiet of bool
    | ConfigNoAssms of bool
    | ConfigEvals of term list
    | ConfigExpect of expectation
    | ConfigMaxCounterexamples of int
    | ConfigTag of string
    | ConfigWidths of int list
    | ConfigQc of qc_config
    | ConfigMf of mf_config

  fun change_config update (cfg : config) =
    { timeout = (case update of ConfigTimeout value => value
                 | _ => #timeout cfg),
      backends = (case update of ConfigBackends value => value
                  | _ => #backends cfg),
      sequential = (case update of ConfigSequential value => value
                    | _ => #sequential cfg),
      genuine_only = (case update of ConfigGenuineOnly value => value
                      | _ => #genuine_only cfg),
      abort_potential = (case update of ConfigAbortPotential value => value
                         | _ => #abort_potential cfg),
      quiet = (case update of ConfigQuiet value => value | _ => #quiet cfg),
      no_assms = (case update of ConfigNoAssms value => value
                  | _ => #no_assms cfg),
      evals = (case update of ConfigEvals value => value | _ => #evals cfg),
      expect = (case update of ConfigExpect value => value
                | _ => #expect cfg),
      max_counterexamples =
        (case update of ConfigMaxCounterexamples value => value
         | _ => #max_counterexamples cfg),
      tag = (case update of ConfigTag value => value | _ => #tag cfg),
      widths = (case update of ConfigWidths value => value
                | _ => #widths cfg),
      qc = (case update of ConfigQc value => value | _ => #qc cfg),
      mf = (case update of ConfigMf value => value | _ => #mf cfg) }

  fun map_qc f (cfg : config) = change_config (ConfigQc (f (#qc cfg))) cfg
  fun map_mf f (cfg : config) = change_config (ConfigMf (f (#mf cfg))) cfg

  fun time_is_representable value =
    (ignore (Time.fromReal value); true) handle Time => false

  fun upd_timeout value =
    if Real.isFinite value andalso value >= 0.0 andalso
       time_is_representable value then
      change_config (ConfigTimeout value)
    else
      raise Feedback.mk_HOL_ERR "Refute_Core" "upd_timeout"
        "timeout: must be a nonnegative representable real"
  fun upd_backends value = change_config (ConfigBackends value)
  fun upd_sequential value = change_config (ConfigSequential value)
  fun upd_genuine_only value = change_config (ConfigGenuineOnly value)
  fun upd_abort_potential value = change_config (ConfigAbortPotential value)
  fun upd_quiet value = change_config (ConfigQuiet value)
  fun upd_no_assms value = change_config (ConfigNoAssms value)
  fun upd_evals value = change_config (ConfigEvals value)
  fun upd_expect value = change_config (ConfigExpect value)
  fun upd_max_counterexamples value =
    if value >= 1 then change_config (ConfigMaxCounterexamples value)
    else raise Feedback.mk_HOL_ERR "Refute_Core" "upd_max_counterexamples"
      "max_counterexamples: must be at least 1"
  fun upd_tag value = change_config (ConfigTag value)
  fun upd_widths value =
    if not (null value) andalso
       List.all (fn width => width >= 1 andalso width <= 32) value then
      change_config (ConfigWidths value)
    else raise Feedback.mk_HOL_ERR "Refute_Core" "upd_widths"
      "widths: must be nonempty with every entry between 1 and 32"

  datatype qc_update =
      QcSize of int * bound_mode
    | QcIterations of int
    | QcDepth of int
    | QcFiniteTypes of bool
    | QcFiniteTypeSize of int
    | QcDefaultType of hol_type list
    | QcSubstrate of substrate_choice
    | QcSeed of int option
    | QcAllowExistentials of bool
    | QcFiniteFunctions of bool
    | QcCertify of bool
    | QcSmartQuantifier of bool
    | QcSmartGenerators of bool
    | QcOptimiseEquality of bool
    | QcReorderPremises of bool
    | QcInstantiate of (hol_type option * hol_type) list
    | QcUseSubtype of bool
    | QcAllowFunctionInversion of bool

  fun change_qc update (qc : qc_config) =
    { size = (case update of QcSize (value, _) => value | _ => #size qc),
      size_mode =
        (case update of QcSize (_, mode) => mode | _ => #size_mode qc),
      iterations = (case update of QcIterations value => value
                    | _ => #iterations qc),
      depth = (case update of QcDepth value => value | _ => #depth qc),
      finite_types = (case update of QcFiniteTypes value => value
                      | _ => #finite_types qc),
      finite_type_size = (case update of QcFiniteTypeSize value => value
                          | _ => #finite_type_size qc),
      default_type = (case update of QcDefaultType value => value
                      | _ => #default_type qc),
      substrate = (case update of QcSubstrate value => value
                   | _ => #substrate qc),
      seed = (case update of QcSeed value => value | _ => #seed qc),
      allow_existentials =
        (case update of QcAllowExistentials value => value
         | _ => #allow_existentials qc),
      finite_functions =
        (case update of QcFiniteFunctions value => value
         | _ => #finite_functions qc),
      certify = (case update of QcCertify value => value | _ => #certify qc),
      smart_quantifier = (case update of QcSmartQuantifier value => value
                          | _ => #smart_quantifier qc),
      smart_generators = (case update of QcSmartGenerators value => value
                          | _ => #smart_generators qc),
      optimise_equality = (case update of QcOptimiseEquality value => value
                           | _ => #optimise_equality qc),
      reorder_premises = (case update of QcReorderPremises value => value
                          | _ => #reorder_premises qc),
      instantiate = (case update of QcInstantiate value => value
                     | _ => #instantiate qc),
      use_subtype = (case update of QcUseSubtype value => value
                     | _ => #use_subtype qc),
      allow_function_inversion =
        (case update of QcAllowFunctionInversion value => value
         | _ => #allow_function_inversion qc) }

  fun validate_qc_config (qc : qc_config) =
    let
      fun invalid field = raise Feedback.mk_HOL_ERR "Refute_Core"
        "validate_qc_config" (field ^ ": must be a bounded nonnegative integer")
      fun bounded field value =
        if value < 0 then invalid field
        else
          case Int.maxInt of
              SOME maximum =>
                if value > maximum div 2 then invalid field else ()
            | NONE => ()
      val _ = bounded "size" (#size qc)
      val _ =
        case #size_mode qc of
            FixedBound => ()
          | IterativeDeepening =>
              if #size qc >= 1 then ()
              else raise Feedback.mk_HOL_ERR "Refute_Core"
                "validate_qc_config"
                "size: iterative initial window must be at least 1"
      val _ = if #iterations qc < 0 then invalid "iterations" else ()
      val _ = bounded "depth" (#depth qc)
      val _ =
        if #finite_type_size qc < 1 orelse #finite_type_size qc > 6 then
          raise Feedback.mk_HOL_ERR "Refute_Core" "validate_qc_config"
            "finite_type_size: must lie between 1 and 6"
        else ()
      val _ = List.app (fn (NONE, _) => ()
                 | (SOME key, _) =>
                     if Type.is_vartype key then ()
                     else raise Feedback.mk_HOL_ERR "Refute_Core"
                       "validate_qc_config"
                       ("instantiate row key must be a type variable; got: " ^
                        Parse.type_to_string key))
        (#instantiate qc)
      (* A pin naming a type that still carries type variables would
         "monomorphize" to a type that is not monomorphic; reject it here
         rather than let it through and rely on the polymorphic guard to
         paper over the incoherence downstream. *)
      val _ = List.app (fn (_, value) =>
                 if null (Type.type_vars value) then ()
                 else raise Feedback.mk_HOL_ERR "Refute_Core"
                   "validate_qc_config"
                   ("instantiate row value must be a ground type (no " ^
                    "type variables); got: " ^ Parse.type_to_string value))
        (#instantiate qc)
    in
      qc
    end

  (* Rebind the record replacement updater too, so callers cannot bypass
     the scalar updater checks with [upd_qc]. *)
  fun upd_qc value (cfg : config) =
    map_qc (fn _ => validate_qc_config value) cfg

  fun update_qc update = map_qc (validate_qc_config o change_qc update)

  fun upd_size value = update_qc (QcSize (value, FixedBound))
  fun upd_iterative_size value =
    update_qc (QcSize (value, IterativeDeepening))
  fun upd_iterations value = update_qc (QcIterations value)
  fun upd_depth value = update_qc (QcDepth value)
  fun upd_finite_types value = update_qc (QcFiniteTypes value)
  fun upd_finite_type_size value = update_qc (QcFiniteTypeSize value)
  fun upd_default_type value = update_qc (QcDefaultType value)
  fun upd_substrate value = update_qc (QcSubstrate value)
  fun upd_seed value = update_qc (QcSeed value)
  fun upd_allow_existentials value =
    update_qc (QcAllowExistentials value)
  fun upd_finite_functions value = update_qc (QcFiniteFunctions value)
  fun upd_certify value = update_qc (QcCertify value)
  fun upd_smart_quantifier value = update_qc (QcSmartQuantifier value)
  fun upd_smart_generators value = update_qc (QcSmartGenerators value)
  fun upd_optimise_equality value = update_qc (QcOptimiseEquality value)
  fun upd_reorder_premises value = update_qc (QcReorderPremises value)
  fun upd_instantiate value = update_qc (QcInstantiate value)
  fun upd_use_subtype value = update_qc (QcUseSubtype value)
  fun upd_allow_function_inversion value =
    update_qc (QcAllowFunctionInversion value)

  fun range_error field explanation =
    raise Feedback.mk_HOL_ERR "Refute_Core" "validate_mf_config"
      (field ^ ": " ^ explanation)

  fun validate_mf_config (mf : mf_config) =
    let
      fun valid_rows field minimum rows =
        if null rows orelse List.exists (fn (_, values) =>
             null values orelse List.exists (fn value => value < minimum)
               values) rows then
          range_error field "rows must be nonempty and values in range"
        else ()
      fun check_term_keys field rows =
        List.app (fn (NONE, _) => ()
                   | (SOME key, _) =>
            if Term.is_const key orelse Term.is_var key then ()
            else range_error field
              ("row key must be a constant or variable; got: " ^
               Parse.term_to_string key)) rows
      val _ = valid_rows "card" 1 (#card mf)
      fun is_prefix values =
        values = List.tabulate (length values, fn index => index + 1)
      val _ =
        case #card_mode mf of
            FixedBound => ()
          | IterativeDeepening =>
              if List.all (is_prefix o #2) (#card mf) then ()
              else range_error "card"
                "iterative rows must be consecutive prefixes [1, ..., n]"
      val _ = valid_rows "max" (~1) (#max mf)
      val _ = check_term_keys "max" (#max mf)
      val _ = check_term_keys "wf" (#wf mf)
      val _ = if null (#bits mf) orelse
                     List.exists (fn bits => bits < 1 orelse bits > 31)
                       (#bits mf) then
                range_error "bits" "values must lie between 1 and 31"
              else ()
      fun can_increment value =
        case Int.maxInt of
            SOME maximum => value < maximum
          | NONE => true
      val _ = if null (#iter mf) orelse
                     List.exists (fn (_, values) => null values orelse
                       List.exists (fn value =>
                         value < 0 orelse not (can_increment value)) values)
                         (#iter mf)
              then range_error "iter"
                "rows must contain values with a representable successor"
              else ()
      val _ = check_term_keys "iter" (#iter mf)
      val _ = if null (#bisim_depth mf) orelse
                     List.exists (fn depth => depth < ~1 orelse
                       (depth >= 0 andalso not (can_increment depth)))
                       (#bisim_depth mf)
              then range_error "bisim_depth"
                "values must be -1 or have a representable successor"
              else ()
      (* A disabled depth requires a context without bisimulation axioms,
         whereas a nonnegative depth requires one with them.  They cannot
         share the preprocessing context used for one MF invocation. *)
      val _ = if List.exists (fn depth => depth < 0) (#bisim_depth mf) andalso
                     List.exists (fn depth => depth >= 0) (#bisim_depth mf)
              then range_error "bisim_depth"
                "do not mix -1 with nonnegative depths"
              else ()
      (* A zero genuine budget makes the model finder return without ever
         calling the solver, which would otherwise be reported as "no
         counterexample" -- indistinguishable from an exhausted search. *)
      val _ = if #max_genuine mf < 1 then
                range_error "max_genuine" "must be at least 1"
              else ()
      val _ = if #max_potential mf < 0 then
                range_error "max_potential" "must not be negative"
              else ()
      val _ =
        case Int.maxInt of
            SOME maximum =>
              if IntInf.fromInt (#max_potential mf) +
                 IntInf.fromInt (#max_genuine mf) > IntInf.fromInt maximum
              then range_error "max_potential"
                "combined solution budget is too large"
              else ()
          | NONE => ()
      val _ = if not (Real.isFinite (#tac_timeout mf)) orelse
                     #tac_timeout mf < 0.0 orelse
                     not (time_is_representable (#tac_timeout mf)) then
                range_error "tac_timeout"
                  "must be a nonnegative representable real"
              else ()
      val _ = if #batch_size mf < 1 then
                range_error "batch_size" "must be at least 1"
              else ()
      val _ = if #datatype_sym_break mf < 0 then
                range_error "datatype_sym_break" "must not be negative"
              else ()
      val _ = if #kodkod_sym_break mf < 0 then
                range_error "kodkod_sym_break" "must not be negative"
              else ()
      val _ = if #max_threads mf < 0 then
                range_error "max_threads" "must not be negative"
              else ()
    in
      mf
    end

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

  fun is_fallback_assign (pattern, _) = not (Option.isSome pattern)

  (* A card list without a [(NONE, _)] entry leaves every type the user did
     not name unassigned, which aborts the backend in [lookup_ints_assign].
     Retain the current fallback; the lookup prefers exact and pattern
     entries, so appending it cannot shadow a user entry. *)
  fun card_with_fallback current value =
    if List.exists is_fallback_assign value then value
    else value @ List.filter is_fallback_assign current

  fun change_mf update (mf : mf_config) =
    { card = (case update of MfCard (value, _) =>
                card_with_fallback (#card mf) value
              | _ => #card mf),
      card_mode =
        (case update of MfCard (_, mode) => mode | _ => #card_mode mf),
      max = (case update of MfMax value => value | _ => #max mf),
      mono = (case update of MfMono value => value | _ => #mono mf),
      wf = (case update of MfWf value => value | _ => #wf mf),
      sat_solver = (case update of MfSatSolver value => value
                    | _ => #sat_solver mf),
      batch_size = (case update of MfBatchSize value => value
                    | _ => #batch_size mf),
      falsify = (case update of MfFalsify value => value
                 | _ => #falsify mf),
      user_axioms = (case update of MfUserAxioms value => value
                     | _ => #user_axioms mf),
      destroy_constrs = (case update of MfDestroyConstrs value => value
                         | _ => #destroy_constrs mf),
      total_consts = (case update of MfTotalConsts value => value
                      | _ => #total_consts mf),
      peephole_optim = (case update of MfPeepholeOptim value => value
                        | _ => #peephole_optim mf),
      datatype_sym_break =
        (case update of MfDatatypeSymBreak value => value
         | _ => #datatype_sym_break mf),
      kodkod_sym_break =
        (case update of MfKodkodSymBreak value => value
         | _ => #kodkod_sym_break mf),
      max_potential = (case update of MfMaxPotential value => value
                       | _ => #max_potential mf),
      max_genuine = (case update of MfMaxGenuine value => value
                     | _ => #max_genuine mf),
      atoms = (case update of MfAtoms value => value | _ => #atoms mf),
      format = (case update of MfFormat value => value | _ => #format mf),
      show_types = (case update of MfShowTypes value => value
                    | _ => #show_types mf),
      show_skolems = (case update of MfShowSkolems value => value
                      | _ => #show_skolems mf),
      show_consts = (case update of MfShowConsts value => value
                     | _ => #show_consts mf),
      debug = (case update of MfDebug value => value | _ => #debug mf),
      overlord = (case update of MfOverlord value => value
                  | _ => #overlord mf),
      max_threads = (case update of MfMaxThreads value => value
                     | _ => #max_threads mf),
      tac_timeout = (case update of MfTacTimeout value => value
                     | _ => #tac_timeout mf),
      specialize = (case update of MfSpecialize value => value
                    | _ => #specialize mf),
      box = (case update of MfBox value => value | _ => #box mf),
      binary_ints = (case update of MfBinaryInts value => value
                     | _ => #binary_ints mf),
      bits = (case update of MfBits value => value | _ => #bits mf),
      star_linear_preds =
        (case update of MfStarLinearPreds value => value
         | _ => #star_linear_preds mf),
      iter = (case update of MfIter value => value | _ => #iter mf),
      bisim_depth = (case update of MfBisimDepth value => value
                     | _ => #bisim_depth mf),
      finitize = (case update of MfFinitize value => value
                  | _ => #finitize mf),
      whack = (case update of MfWhack value => value | _ => #whack mf),
      need = (case update of MfNeed value => value | _ => #need mf),
      merge_type_vars =
        (case update of MfMergeTypeVars value => value
         | _ => #merge_type_vars mf) }

  fun upd_mf value = map_mf (fn _ => validate_mf_config value)

  fun update_mf update = map_mf (validate_mf_config o change_mf update)

  fun upd_card value = update_mf (MfCard (value, FixedBound))
  fun upd_iterative_card value =
    update_mf (MfCard (value, IterativeDeepening))
  fun upd_max value = update_mf (MfMax value)
  fun upd_mono value = update_mf (MfMono value)
  fun upd_wf value = update_mf (MfWf value)
  fun upd_sat_solver value = update_mf (MfSatSolver value)
  fun upd_batch_size value = update_mf (MfBatchSize value)
  fun upd_falsify value = update_mf (MfFalsify value)
  fun upd_user_axioms value = update_mf (MfUserAxioms value)
  fun upd_destroy_constrs value = update_mf (MfDestroyConstrs value)
  fun upd_total_consts value = update_mf (MfTotalConsts value)
  fun upd_peephole_optim value = update_mf (MfPeepholeOptim value)
  fun upd_datatype_sym_break value = update_mf (MfDatatypeSymBreak value)
  fun upd_kodkod_sym_break value = update_mf (MfKodkodSymBreak value)
  fun upd_max_potential value = update_mf (MfMaxPotential value)
  fun upd_max_genuine value = update_mf (MfMaxGenuine value)
  fun upd_atoms value = update_mf (MfAtoms value)
  fun upd_format value = update_mf (MfFormat value)
  fun upd_show_types value = update_mf (MfShowTypes value)
  fun upd_show_skolems value = update_mf (MfShowSkolems value)
  fun upd_show_consts value = update_mf (MfShowConsts value)
  fun upd_debug value = update_mf (MfDebug value)
  fun upd_overlord value = update_mf (MfOverlord value)
  fun upd_max_threads value = update_mf (MfMaxThreads value)
  fun upd_tac_timeout value = update_mf (MfTacTimeout value)
  fun upd_specialize value = update_mf (MfSpecialize value)
  fun upd_box value = update_mf (MfBox value)
  fun upd_binary_ints value = update_mf (MfBinaryInts value)
  fun upd_bits value = update_mf (MfBits value)
  fun upd_star_linear_preds value = update_mf (MfStarLinearPreds value)
  fun upd_iter value = update_mf (MfIter value)
  fun upd_bisim_depth value = update_mf (MfBisimDepth value)
  fun upd_finitize value = update_mf (MfFinitize value)
  fun upd_whack value = update_mf (MfWhack value)
  fun upd_need value = update_mf (MfNeed value)
  fun upd_merge_type_vars value = update_mf (MfMergeTypeVars value)

  fun strip_outer_forall tm = boolSyntax.strip_forall tm

  fun strip_outer_forall_body tm = #2 (strip_outer_forall tm)

  val bounded_rewrites =
    [ refuteTheory.bounded_forall_less,
      refuteTheory.bounded_exists_less,
      refuteTheory.bounded_forall_leq,
      refuteTheory.bounded_exists_leq,
      refuteTheory.bounded_forall_in_count,
      refuteTheory.bounded_exists_in_count,
      refuteTheory.bounded_forall_mem,
      refuteTheory.bounded_exists_mem,
      refuteTheory.bounded_forall_interval_leq_lt,
      refuteTheory.bounded_exists_interval_leq_lt,
      refuteTheory.bounded_forall_interval_leq_lt_swap,
      refuteTheory.bounded_exists_interval_leq_lt_swap,
      refuteTheory.bounded_forall_interval_leq_leq,
      refuteTheory.bounded_exists_interval_leq_leq,
      refuteTheory.bounded_forall_interval_leq_leq_swap,
      refuteTheory.bounded_exists_interval_leq_leq_swap,
      refuteTheory.bounded_forall_interval_lt_lt,
      refuteTheory.bounded_exists_interval_lt_lt,
      refuteTheory.bounded_forall_interval_lt_lt_swap,
      refuteTheory.bounded_exists_interval_lt_lt_swap,
      refuteTheory.bounded_forall_interval_lt_leq,
      refuteTheory.bounded_exists_interval_lt_leq,
      refuteTheory.bounded_forall_interval_lt_leq_swap,
      refuteTheory.bounded_exists_interval_lt_leq_swap ]

  val normal_rewrites =
    [ boolTheory.NOT_EXISTS_THM,
      boolTheory.NOT_FORALL_THM,
      boolTheory.AND_IMP_INTRO,
      boolTheory.FUN_EQ_THM ] @
    bounded_rewrites @
    Drule.CONJUNCTS boolTheory.PULL_EXISTS @
    Drule.CONJUNCTS boolTheory.PULL_FORALL

  fun has_bounded_quantifier tm =
    let
      (* Every bound predicate excludes [variable] from the other side:
         e.g. [f n <= n] or [n < f n] put [variable] on the expected side
         syntactically, but the rewrite these predicates predict needs
         [lo]/[e] free of [variable] to instantiate under the binder. *)
      fun bound_left dest variable guard =
        case Lib.total dest guard of
            SOME (left, right) =>
              Term.aconv left variable andalso
              not (Term.free_in variable right)
          | NONE => false
      fun bound_right dest variable guard =
        case Lib.total dest guard of
            SOME (left, right) =>
              Term.aconv right variable andalso
              not (Term.free_in variable left)
          | NONE => false
      fun in_count variable guard =
        case Lib.total pred_setSyntax.dest_in guard of
            SOME (element, set) =>
              Term.aconv element variable andalso
              (case Lib.total pred_setSyntax.dest_count set of
                   SOME bound => not (Term.free_in variable bound)
                 | NONE => false)
          | NONE => false
      fun in_list variable guard =
        case Lib.total listSyntax.dest_mem guard of
            SOME (element, list) =>
              Term.aconv element variable andalso
              not (Term.free_in variable list)
          | NONE => false
      (* An upper bound has [variable] on the left ([n < e], [n <= e]) or
         as the tested element ([n IN count e], [MEM n l]) -- the shape
         the plain, non-interval rewrites already recognise. *)
      fun upper_bound variable guard =
        bound_left numSyntax.dest_less variable guard orelse
        bound_left numSyntax.dest_leq variable guard orelse
        in_count variable guard orelse in_list variable guard
      (* An interval's upper bound is numeric-only: [in_count]/[in_list]
         have no interval rewrite ([bounded_forall_mem] needs its
         antecedent to be exactly [MEM n l], and every interval theorem
         needs both conjuncts to be [numSyntax] comparisons), so mixing
         them into [interval_pair] would admit shapes no rewrite covers. *)
      fun interval_upper_bound variable guard =
        bound_left numSyntax.dest_less variable guard orelse
        bound_left numSyntax.dest_leq variable guard
      (* A lower bound has [variable] on the right ([lo < n], [lo <= n]),
         the new half of an offset interval. *)
      fun lower_bound variable guard =
        bound_right numSyntax.dest_less variable guard orelse
        bound_right numSyntax.dest_leq variable guard
      fun interval_pair variable g1 g2 =
        (lower_bound variable g1 andalso
         interval_upper_bound variable g2) orelse
        (interval_upper_bound variable g1 andalso
         lower_bound variable g2)
      (* Forall's guard is one conjunction after [AND_IMP_INTRO] merges
         nested implications; exists' guard is the first conjunct of a
         three-way [g1 /\ g2 /\ P n], so its interval pair sits one level
         deeper, behind [rest]. *)
      fun bounded variable body universal =
        if universal then
          case Lib.total boolSyntax.dest_imp body of
              SOME (guard, _) =>
                upper_bound variable guard orelse
                (case Lib.total boolSyntax.dest_conj guard of
                     SOME (g1, g2) => interval_pair variable g1 g2
                   | NONE => false)
            | NONE => false
        else
          case Lib.total boolSyntax.dest_conj body of
              SOME (g1, rest) =>
                upper_bound variable g1 orelse
                (case Lib.total boolSyntax.dest_conj rest of
                     SOME (g2, _) => interval_pair variable g1 g2
                   | NONE => false)
            | NONE => false
      fun search tm =
        if boolSyntax.is_forall tm orelse boolSyntax.is_exists tm then
          let
            val universal = boolSyntax.is_forall tm
            val (variable, body) =
              if universal then boolSyntax.dest_forall tm
              else boolSyntax.dest_exists tm
          in
            bounded variable body universal orelse search body
          end
        else if Term.is_comb tm then
          let val (left, right) = Term.dest_comb tm
          in search left orelse search right end
        else if Term.is_abs tm then
          search (Term.body tm)
        else
          false
    in
      search tm
    end

  fun normalize tm =
    #2 (boolSyntax.dest_eq (Thm.concl
      (Ho_Rewrite.REWRITE_CONV normal_rewrites tm)))
    handle Interrupt => raise Interrupt
         | _ => tm

  fun expand_quantifiers tm =
    let
      fun expand tm =
        if boolSyntax.is_forall tm then
          let
            val (variable, body) = boolSyntax.dest_forall tm
            val body = expand body
          in
            case Refute_Gen.enumerate (Term.type_of variable) of
                NONE => boolSyntax.mk_forall (variable, body)
              | SOME values =>
                  boolSyntax.list_mk_conj
                    (map (fn value => Term.subst
                      [{redex = variable, residue = value}] body)
                      values)
          end
        else if boolSyntax.is_exists tm then
          let
            val (variable, body) = boolSyntax.dest_exists tm
            val body = expand body
          in
            case Refute_Gen.enumerate (Term.type_of variable) of
                NONE => boolSyntax.mk_exists (variable, body)
              | SOME values =>
                  boolSyntax.list_mk_disj
                    (map (fn value => Term.subst
                      [{redex = variable, residue = value}] body)
                      values)
          end
        else if Term.is_comb tm then
          let
            val (left, right) = Term.dest_comb tm
          in
            Term.mk_comb (expand left, expand right)
          end
        else if Term.is_abs tm then
          let
            val (variable, body) = Term.dest_abs tm
          in
            Term.mk_abs (variable, expand body)
          end
        else
          tm
    in
      expand tm
    end

  fun has_unexpanded_binder tm =
    if boolSyntax.is_forall tm orelse boolSyntax.is_exists tm orelse
       boolSyntax.is_select tm then
      true
    else if Term.is_abs tm then
      has_unexpanded_binder (Term.body tm)
    else if Term.is_comb tm then
      let
        val (left, right) = Term.dest_comb tm
      in
        has_unexpanded_binder left orelse has_unexpanded_binder right
      end
    else
      false

  (* [[real_of_num]] is [[nocompute]] -- it carries no compset entry of
     its own, unlike [[rat_of_num]], which unfolds via a genuine (if
     unused in practice) SUC-recursive definition -- yet a ground real
     numeral or [[n / d]] fraction built from it is exactly as much a
     closed, already-decided value as a NUMERAL literal: realSimps'
     rules pattern-match through [[real_of_num]]/[[real_neg]]/[[real_div]]
     directly, never by unfolding [[real_of_num]] itself.  Recognise that
     shape the same way [[Literal.is_literal]] recognises a bare numeral,
     so it is never mistaken for a stuck, non-executable constant.

     A fraction of two real literals is only ever actually decided by
     the compset when the numerator is zero (unconditional, by
     [[REAL_DIV_LZERO]]) or the denominator is a nonzero literal
     (negative denominators are first renormalised by [[realSimps]]'
     [[div_rats]]/[[div_ratls]]/[[div_ratrs]], positive ones handled
     directly): this is exactly [[realSimps.elim_common_factor]]'s own
     acceptance condition, which raises on a nonzero numerator over a
     zero denominator and so leaves it stuck.  Match that condition
     here so a term like [[1 / 0]] is not mistaken for a decided value. *)
  fun is_real_literal_fraction tm =
    realSyntax.is_div tm andalso
    let val (num, den) = realSyntax.dest_div tm in
      realSyntax.is_real_literal num andalso realSyntax.is_real_literal den
    end

  fun is_real_numeral_value tm =
    realSyntax.is_real_literal tm orelse
    (is_real_literal_fraction tm andalso
     let val (num, den) = realSyntax.dest_div tm in
       realSyntax.int_of_term num = Arbint.zero orelse
       realSyntax.int_of_term den <> Arbint.zero
     end)

  fun term_constants tm =
    let
      fun collect seen tm =
        if Literal.is_literal tm orelse is_real_numeral_value tm then
          (* Numeral/string/char literals are closed values that EVAL
             reduces natively; their internal constants (NUMERAL, BIT1,
             STRING, CHR, ...) never leave the evaluator stuck.  A real
             numeral value is the same, despite [[real_of_num]] itself
             having no compset entry -- see [[is_real_numeral_value]]. *)
          seen
        else if is_real_literal_fraction tm then
          (* Rejected by [[is_real_numeral_value]]: a nonzero numerator
             over a zero denominator, which [[elim_common_factor]]
             declines.  Generic recursion below would only reach
             [[real_div]], which the compset can otherwise decide, and
             lose the fact that this particular redex is stuck; surface
             [[real_of_num]] (genuinely [[nocompute]]) directly instead. *)
          if List.exists
               (fn old => Term.same_const old realSyntax.real_injection)
               seen
          then seen
          else realSyntax.real_injection :: seen
        else if Term.is_const tm then
          if List.exists (fn old => Term.same_const old tm) seen then seen
          else tm :: seen
        else if Term.is_comb tm then
          let
            val (left, right) = Term.dest_comb tm
          in
            collect (collect seen left) right
          end
        else if Term.is_abs tm then
          collect seen (Term.body tm)
        else
          seen
    in
      collect [] tm
    end

  fun nonexecutable_constants terms =
    let
      val comp_items = computeLib.listItems (computeLib.the_compset ())
      val executable_keys =
        List.foldl (fn ((key, transforms), keys) =>
          if null transforms then keys else Redblackset.add (keys, key))
          (Redblackset.empty
            (Portable.pair_compare (String.compare, String.compare)))
          comp_items
      fun executable_constant constant =
        TypeBase.is_constructor constant orelse
        Refute_Gen.is_family_constructor constant orelse
        let
          val {Name, Thy, ...} = Term.dest_thy_const constant
        in
          Redblackset.member (executable_keys, (Name, Thy))
        end
      fun add (term, constants) =
        List.foldl (fn (constant, collected) =>
          if List.exists (fn old => Term.same_const old constant) collected
          then collected
          else constant :: collected) constants (term_constants term)
      val constants = List.foldl add [] terms
    in
      List.filter (not o executable_constant) constants
    end

  fun show_constants constants =
    String.concatWith ", "
      (Listsort.sort String.compare
        (map Parse.term_to_string constants))

  fun rf_type number =
    Type.mk_thy_type
      { Thy = "refute", Tyop = "rf" ^ Int.toString number, Args = [] }

  (* A type variable in the index position of a [cart] - the width slot of
     a machine word - cannot take an [rf] carrier: nothing computes
     [dimindex (:rf1)], so every substrate declines.  Such a variable is
     instantiated to an fcp numeral type instead.  Index occurrence wins
     over a value-position occurrence of the same variable. *)
  fun width_type_vars tys =
    let
      fun collect (ty, found) =
        let
          val found =
            case Lib.total fcpSyntax.dest_cart_type ty of
                SOME (_, index_ty) =>
                  Lib.union (Type.type_vars index_ty) found
              | NONE => found
        in
          List.foldl collect found
            (#2 (Type.dest_type ty) handle Feedback.HOL_ERR _ => [])
        end
    in
      List.foldl collect [] tys
    end

  fun monomorphic_types qc =
    if #finite_types qc then
      List.tabulate (#finite_type_size qc, fn index => rf_type (index + 1))
    else
      #default_type qc

  fun add_equation_eval_terms goal evals =
    let
      val (_, conclusion) = boolSyntax.strip_imp goal
    in
      case Lib.total boolSyntax.dest_eq conclusion of
          SOME (left, right) =>
            if Term.is_var left orelse Term.is_var right then evals
            else evals @ [left, right]
        | NONE => evals
    end

  fun instance_size_matters goal =
    List.exists (fn variable =>
      not (Option.isSome (Refute_Gen.enumerate (Term.type_of variable))))
      (Term.free_vars_lr goal)

  (* Shared by [make_instance] and [Refute_QC]'s [use_subtype] transform,
     which recomputes this for the rewritten goal: a syntactic executability
     scan, not a claim about what testing does at a concrete value. *)
  fun compute_qc_gate goal evals =
    let
      val binders_remain = has_unexpanded_binder goal
      val constants =
        if binders_remain then []
        else nonexecutable_constants (goal :: evals)
    in
      if binders_remain then SOME ["not executable: unexpanded binder"]
      else if null constants then NONE
      else SOME ["not executable: " ^ show_constants constants]
    end

  type preprocessed_forms =
    {mono_instances : instance list, poly_original : instance list}

  (* Installed by [Refute_QC] at load time with the [use_subtype] rewrite:
     [Refute_ModelFinder_HOL] owns the typedef harvest the transform needs
     and already depends on this structure, so [Refute_Core] cannot call
     into it directly; the transform is threaded in as a callback instead,
     on the same precedent as [register_backend] below.  Applied only to
     [MonoInstances] instances, in [preprocess_forms]; [PolyOriginal]
     instances (the model finder's input) never reach it. *)
  val mono_instance_transform : (config -> instance -> instance) ref =
    ref (fn (_ : config) => fn (instance : instance) => instance)

  fun register_mono_instance_transform f = mono_instance_transform := f

  (* A configuration error diagnosed while building the instances, e.g. an
     [upd_instantiate] pin naming a type variable absent from the goal.
     Its own exception, on the [Refute_Gen.NoGenerator] precedent, so the
     handler in [attempt] can render one clean line instead of letting it
     fall to the generic [exception_reason] dump. *)
  exception InstantiateError of string

  fun preprocess_forms (cfg : config) (problem : problem) =
    let
      val assumptions =
        if #no_assms cfg then [] else #assumptions problem
      val unrenamed_goal =
        boolSyntax.list_mk_imp (assumptions, #goal problem)
      val unrenamed_evals = #evals problem @ #evals cfg
      (* `_` is the shared model/narrowing marker.  Vary a colliding user
         free once for every backend, before any marker can be introduced. *)
      val (renamed, _) = Names.rename_irrelevant_collisions
        (unrenamed_goal :: unrenamed_evals)
      val original_goal = hd renamed
      val input_evals = tl renamed
      val types = monomorphic_types (#qc cfg)
      val input_terms = original_goal :: input_evals
      val tyvars = Lib.U (map Term.type_vars_in_term input_terms)
      val width_vars = width_type_vars
        (map Term.type_of
          (List.concat (map (HolKernel.find_terms (Lib.K true)) input_terms)))
      val widths = #widths cfg
      val instantiate = #instantiate (#qc cfg)
      fun instantiate_error message = raise InstantiateError message
      val () = List.app (fn (NONE, _) => ()
                 | (SOME tyvar, _) =>
                     if Lib.mem tyvar tyvars then ()
                     else instantiate_error
                       ("type variable " ^ Parse.type_to_string tyvar ^
                        " does not occur in the goal")) instantiate
      (* [Refute_ModelFinder_Util.double_lookup] is the same SOME-then-NONE
         shape, but does not fit: its NONE branch is unconditional, and a
         width variable must never take the NONE fallback (see
         [resolved_pin] below), which needs a guard double_lookup has no
         room for. *)
      fun instantiate_lookup tyvar =
        case List.find (fn (SOME key, _) => Refute_Util.same_type key tyvar
                          | (NONE, _) => false) instantiate of
            SOME (_, pin) => SOME pin
          | NONE =>
              if Lib.mem tyvar width_vars then NONE
              else Option.map #2
                (List.find (fn (NONE, _) => true | _ => false) instantiate)
      (* Resolved once per tyvar, independently of [card]: a pin never
         varies across instances, so this also catches a malformed width
         pin before any instance is built. *)
      fun resolved_pin tyvar =
        case instantiate_lookup tyvar of
            NONE => NONE
          | SOME pin =>
              if Lib.mem tyvar width_vars andalso
                 not (fcpSyntax.is_numeric_type pin) then
                instantiate_error
                  ("width type variable " ^ Parse.type_to_string tyvar ^
                   " must be pinned to a concrete word-width type " ^
                   "(:1, :2, ...), not " ^ Parse.type_to_string pin)
              else SOME pin
      val pin_table = List.mapPartial
        (fn tyvar => Option.map (fn pin => (tyvar, pin)) (resolved_pin tyvar))
        tyvars
      val pinned_vars = map #1 pin_table
      val unpinned_tyvars =
        List.filter (fn tyvar => not (Lib.mem tyvar pinned_vars)) tyvars
      val unpinned_width_vars =
        List.filter (fn tyvar => Lib.mem tyvar unpinned_tyvars) width_vars
      fun make_instance card theta =
        let
          val original = Term.inst theta original_goal
          val initial_goal = strip_outer_forall_body original
          val normalized_goal =
            strip_outer_forall_body (normalize initial_goal)
          val goal = expand_quantifiers normalized_goal
          val evals = map (Term.inst theta) input_evals
          val evals = add_equation_eval_terms goal evals
        in
          { original = original,
            goal = goal,
            qc_gate = compute_qc_gate goal evals,
            evals = evals,
            card = card,
            size_matters = instance_size_matters goal,
            transport = [] }
        end
      (* One replacement interprets every *unpinned* type variable at once
         (see [upd_instantiate]), so [card] is the index of the single
         carrier/width pair the instance uses for them.  That identity is
         what lets [Refute_QC.schedule] order work by [card + size] and
         lets every report name the cardinality it tested.  Interpreting
         the variables independently would instead normalize
         [finite_type_size] raised to the number of type variables
         instances before any backend runs, and leave [card] a bare
         dispatch index.  For the same reason the two roles are paired by
         clamped index rather than crossed.  A pinned variable is fixed to
         its own type in every instance and never participates in this
         indexing; a fully pinned goal ([unpinned_tyvars] empty) therefore
         collapses to exactly one instance -- unless the goal has a
         symbolic word width, since [NONE] never pins one (see
         [instantiate_lookup]), so an otherwise fully-[SOME]-pinned goal
         with an unpinned width variable still varies over [widths]. *)
      val instance_count =
        if null unpinned_tyvars then 1
        else if null types then 0
        else if null unpinned_width_vars then length types
        else Int.max (length types, length widths)
      fun monomorphic_instance card =
        let
          (* Thunked, not [val]: [types] can be empty ([upd_default_type]
             has no lower-bound check), and a fully pinned goal now needs
             zero carrier lookups where the old code always needed one, so
             an eager [List.nth] would raise [Subscript] on that goal. Safe
             because [carrier]/[width] are only forced for an unpinned
             tyvar, and a fully pinned goal has none. *)
          fun carrier () = List.nth (types, Int.min (card, length types) - 1)
          fun width () = fcpSyntax.mk_int_numeric_type
            (List.nth (widths, Int.min (card, length widths) - 1))
          fun residue tyvar =
            case List.find (fn (pinned, _) => Refute_Util.same_type pinned
                              tyvar) pin_table of
                SOME (_, pin) => pin
              | NONE => if Lib.mem tyvar width_vars then width ()
                        else carrier ()
        in
          make_instance card
            (map (fn tyvar => {redex = tyvar, residue = residue tyvar})
               tyvars)
        end
      val raw_mono_instances =
        if null tyvars then [make_instance 1 []]
        else
          List.tabulate (instance_count, fn index =>
            monomorphic_instance (index + 1))
      (* Absent the [use_subtype] transform, a monomorphic goal hands both
         forms literally the same backend input -- stronger than merely
         constructing an equivalent singleton, and it keeps the old
         front-end behaviour exact.  Read it off [raw_mono_instances],
         before the transform runs below: the model finder handles
         typedefs natively and must never see the rewrite, so when the
         transform does fire the two forms deliberately diverge and
         [poly_original] keeps the untransported goal. *)
      val poly_original =
        if null tyvars then raw_mono_instances else [make_instance 0 []]
      val mono_instances =
        map (!mono_instance_transform cfg) raw_mono_instances
    in
      {mono_instances = mono_instances, poly_original = poly_original}
    end

  fun preprocess cfg problem =
    #mono_instances (preprocess_forms cfg problem)

  fun instances_for_form MonoInstances
        ({mono_instances, ...} : preprocessed_forms) = mono_instances
    | instances_for_form PolyOriginal {poly_original, ...} = poly_original

  (* Exhausting the finitely many monomorphic QC proxies does not exhaust a
     polymorphic HOL type.  Keep that miss bounds-relative at the common
     backend boundary, before it can become a decisive whole-space result. *)
  fun forms_are_polymorphic
        ({poly_original, ...} : preprocessed_forms) =
    List.exists (fn (instance : instance) =>
      List.exists (not o null o Term.type_vars_in_term)
        (#original instance :: #evals instance)) poly_original

  fun preserve_polymorphic_bounds (backend : backend)
        (forms : preprocessed_forms)
        (instances : instance list) result =
    case (#input backend, forms_are_polymorphic forms, result) of
        (MonoInstances, true, NoCounterexample) =>
          let
            val cards = map (Int.toString o #card) instances
          in
            Unknown
              ["polymorphic search covered only configured monomorphic " ^
               "proxies" ^
               (if null cards then ""
                else " at indices " ^
                  String.concatWith ", " cards)]
          end
      | _ => result

  structure Private = struct
    val trace = ref 1
    val _ = Feedback.register_trace ("Refute", trace, 4)

    fun enabled level = !trace >= level

    fun say level message =
      if enabled level then Feedback.HOL_MESG message else ()

    fun expectation_to_string NoExpectation = "NoExpectation"
      | expectation_to_string ExpectNone = "ExpectNone"
      | expectation_to_string ExpectUnknown = "ExpectUnknown"
      | expectation_to_string ExpectCex = "ExpectCex"
      | expectation_to_string ExpectModel = "ExpectModel"
      | expectation_to_string ExpectNoModel = "ExpectNoModel"
      | expectation_to_string ExpectGenuine = "ExpectGenuine"
      | expectation_to_string ExpectQuasiGenuine =
          "ExpectQuasiGenuine"
      | expectation_to_string ExpectPotential = "ExpectPotential"

    fun substrate_to_string Auto = "Auto"
      | substrate_to_string Compute = "Compute"
      | substrate_to_string Cv = "Cv"
      | substrate_to_string NativeSML = "NativeSML"

    fun bound_mode_to_string FixedBound = "FixedBound"
      | bound_mode_to_string IterativeDeepening = "IterativeDeepening"

    fun option_to_string f NONE = "NONE"
      | option_to_string f (SOME x) = "SOME " ^ f x
  end

  fun show_config () =
    let
      val {timeout, backends, sequential, genuine_only, abort_potential,
           quiet, no_assms, evals, expect, max_counterexamples, tag, widths,
           qc, mf} =
        !the_config
      val q = qc
      val m = mf
      val show = Private.say 1
      val types = String.concatWith ", " (map Parse.type_to_string
        (#default_type q))
      fun list_to_string f values =
        "[" ^ String.concatWith ", " (map f values) ^ "]"
      val ints = list_to_string Int.toString
      val strings = list_to_string (fn value => "\"" ^ value ^ "\"")
      val terms = list_to_string Parse.term_to_string
      fun assignments key_to_string value_to_string rows =
        list_to_string
          (fn (key, value) =>
            Private.option_to_string key_to_string key ^ " => " ^
              value_to_string value)
          rows
      val type_ints = assignments Parse.type_to_string ints
      val term_ints = assignments Parse.term_to_string ints
      val type_bools = assignments Parse.type_to_string
        (Private.option_to_string Bool.toString)
      val term_bools = assignments Parse.term_to_string
        (Private.option_to_string Bool.toString)
      val type_strings = assignments Parse.type_to_string strings
      val type_types = assignments Parse.type_to_string Parse.type_to_string
      fun optional_terms NONE = "NONE"
        | optional_terms (SOME values) = "SOME " ^ terms values
    in
      List.app show
        [ "timeout = " ^ Real.toString timeout ^ "\n",
          "backends = " ^ Private.option_to_string
            (String.concatWith ", ") backends ^ "\n",
          "sequential = " ^ Bool.toString sequential ^ "\n",
          "genuine_only = " ^ Bool.toString genuine_only ^ "\n",
          "abort_potential = " ^ Bool.toString abort_potential ^ "\n",
          "quiet = " ^ Bool.toString quiet ^ "\n",
          "no_assms = " ^ Bool.toString no_assms ^ "\n",
          "evals = " ^ Int.toString (length evals) ^ " terms\n",
          "expect = " ^ Private.expectation_to_string expect ^ "\n",
          "max_counterexamples = " ^ Int.toString max_counterexamples ^ "\n",
          "tag = " ^ tag ^ "\n",
          "widths = " ^ ints widths ^ "\n",
          "size = " ^ Int.toString (#size q) ^ "\n",
          "size_mode = " ^ Private.bound_mode_to_string (#size_mode q) ^
            "\n",
          "iterations = " ^ Int.toString (#iterations q) ^ "\n",
          "depth = " ^ Int.toString (#depth q) ^ "\n",
          "finite_types = " ^ Bool.toString (#finite_types q) ^
            "\n",
          "finite_type_size = " ^ Int.toString (#finite_type_size q) ^
            "\n",
          "default_type = " ^ types ^ "\n",
          "instantiate = " ^ type_types (#instantiate q) ^ "\n",
          "substrate = " ^ Private.substrate_to_string (#substrate q) ^
            "\n",
          "seed = " ^ Private.option_to_string Int.toString (#seed q) ^
            "\n",
          "allow_existentials = " ^
            Bool.toString (#allow_existentials q) ^ "\n",
          "finite_functions = " ^
            Bool.toString (#finite_functions q) ^ "\n",
          "certify = " ^ Bool.toString (#certify q) ^ "\n",
          "smart_quantifier = " ^
            Bool.toString (#smart_quantifier q) ^ "\n",
          "smart_generators = " ^
            Bool.toString (#smart_generators q) ^ "\n",
          "optimise_equality = " ^
            Bool.toString (#optimise_equality q) ^ "\n",
          "reorder_premises = " ^
            Bool.toString (#reorder_premises q) ^ "\n",
          "use_subtype = " ^ Bool.toString (#use_subtype q) ^ "\n",
          "allow_function_inversion = " ^
            Bool.toString (#allow_function_inversion q) ^ "\n",
          "mf.card = " ^ type_ints (#card m) ^ "\n",
          "mf.card_mode = " ^
            Private.bound_mode_to_string (#card_mode m) ^ "\n",
          "mf.max = " ^ term_ints (#max m) ^ "\n",
          "mf.mono = " ^ type_bools (#mono m) ^ "\n",
          "mf.wf = " ^ term_bools (#wf m) ^ "\n",
          "mf.sat_solver = " ^ #sat_solver m ^ "\n",
          "mf.batch_size = " ^ Int.toString (#batch_size m) ^ "\n",
          "mf.falsify = " ^ Bool.toString (#falsify m) ^ "\n",
          "mf.user_axioms = " ^ Private.option_to_string Bool.toString
            (#user_axioms m) ^ "\n",
          "mf.destroy_constrs = " ^ Bool.toString (#destroy_constrs m) ^
            "\n",
          "mf.total_consts = " ^ Private.option_to_string Bool.toString
            (#total_consts m) ^ "\n",
          "mf.peephole_optim = " ^ Bool.toString (#peephole_optim m) ^
            "\n",
          "mf.datatype_sym_break = " ^
            Int.toString (#datatype_sym_break m) ^ "\n",
          "mf.kodkod_sym_break = " ^
            Int.toString (#kodkod_sym_break m) ^ "\n",
          "mf.max_potential = " ^ Int.toString (#max_potential m) ^ "\n",
          "mf.max_genuine = " ^ Int.toString (#max_genuine m) ^ "\n",
          "mf.atoms = " ^ type_strings (#atoms m) ^ "\n",
          "mf.format = " ^ term_ints (#format m) ^ "\n",
          "mf.show_types = " ^ Bool.toString (#show_types m) ^ "\n",
          "mf.show_skolems = " ^ Bool.toString (#show_skolems m) ^ "\n",
          "mf.show_consts = " ^ Bool.toString (#show_consts m) ^ "\n",
          "mf.debug = " ^ Bool.toString (#debug m) ^ "\n",
          "mf.overlord = " ^ Bool.toString (#overlord m) ^ "\n",
          "mf.max_threads = " ^ Int.toString (#max_threads m) ^ "\n",
          "mf.tac_timeout = " ^ Real.toString (#tac_timeout m) ^ "\n",
          "mf.specialize = " ^ Bool.toString (#specialize m) ^ "\n",
          "mf.box = " ^ type_bools (#box m) ^ "\n",
          "mf.binary_ints = " ^ Private.option_to_string Bool.toString
            (#binary_ints m) ^ "\n",
          "mf.bits = " ^ ints (#bits m) ^ "\n",
          "mf.star_linear_preds = " ^
            Bool.toString (#star_linear_preds m) ^ "\n",
          "mf.iter = " ^ term_ints (#iter m) ^ "\n",
          "mf.bisim_depth = " ^ ints (#bisim_depth m) ^ "\n",
          "mf.finitize = " ^ type_bools (#finitize m) ^ "\n",
          "mf.whack = " ^ terms (#whack m) ^ "\n",
          "mf.need = " ^ optional_terms (#need m) ^ "\n",
          "mf.merge_type_vars = " ^ Bool.toString (#merge_type_vars m) ^
            "\n" ]
    end

  val backend_registry : (string * backend_registration) list ref = ref []
  val registry_mutex = Mutex.mutex ()

  fun synchronized_registry f =
    Multithreading.synchronized "Refute_Core.registry" registry_mutex f

  (* Deciding whether a backend is eligible can compile and park resources
     (the QC smart-generator gate compiles a trial test).  A backend that is
     never run, or is killed by the parallel race, cannot release them
     itself, so holders register a run-scoped release here; it runs on every
     exit path of [refute_problem_unquiet]. *)
  val run_releases : (string * (unit -> unit)) list ref = ref []

  (* Registrations are made when implementation units are loaded, so give
     releases stable names and replace an old registration on reload. *)
  fun release_actions actions =
    let
      fun release ((_, close), NONE) =
            (case Exn.capture close () of
                 Exn.Res _ => NONE
               | Exn.Exn error => SOME error)
        | release ((_, close), first) =
            (ignore (Exn.capture close ()); first)
    in
      case List.foldl release NONE actions of
          NONE => ()
        | SOME error => raise error
    end

  fun register_run_release name release =
    synchronized_registry (fn () =>
      run_releases :=
        List.filter (fn (old_name, _) => old_name <> name) (!run_releases) @
        [(name, release)])

  fun release_run_resources () =
    release_actions (synchronized_registry (fn () => !run_releases))

  fun backend_before (left : string * backend_registration)
      (right : string * backend_registration) =
    #weight (#backend (#2 left)) < #weight (#backend (#2 right)) orelse
    (#weight (#backend (#2 left)) = #weight (#backend (#2 right)) andalso
     #1 left < #1 right)

  fun insert_backend entry [] = [entry]
    | insert_backend entry (other :: rest) =
        if backend_before entry other then entry :: other :: rest
        else other :: insert_backend entry rest

  fun register_backend_with_ceiling backend certainty_ceiling =
    synchronized_registry (fn () =>
      let
        val without_old =
          List.filter (fn (name, _) => name <> #name backend)
            (!backend_registry)
        val registration =
          {backend = backend, certainty_ceiling = certainty_ceiling}
        val entry = (#name backend, registration)
      in
        backend_registry := insert_backend entry without_old
      end)

  fun register_backend backend =
    (* Backends that declare no tighter, configuration-sensitive bound get
       the conservative Genuine ceiling. *)
    register_backend_with_ceiling backend (fn _ => fn _ => Genuine)

  fun registered_backends () =
    synchronized_registry (fn () => map (#backend o #2) (!backend_registry))

  fun lookup_backend name =
    synchronized_registry (fn () =>
      Option.map (#backend o #2)
        (List.find (fn (registered, _) => registered = name)
          (!backend_registry)))

  fun resolve_backend_registrations names =
    let
      val snapshot = synchronized_registry (fn () => !backend_registry)
      fun requested (registration : backend_registration) =
        case names of
            NONE => true
          | SOME wanted => List.exists
              (fn name => name = #name (#backend registration)) wanted
      fun registered name =
        List.exists (fn (registered, _) => registered = name) snapshot
      val registrations = map #2
        (List.filter (fn (_, registration) => requested registration) snapshot)
      val unknown =
        case names of
            NONE => []
          | SOME wanted => List.filter (not o registered) wanted
    in
      (registrations, unknown)
    end

  fun lookup_stat key stats =
    Option.map #2 (List.find (fn (name, _) => name = key) stats)

  fun format_stats stats =
    let
      val msec =
        case lookup_stat "msec" stats of
            NONE => NONE
          | SOME value => SOME
              (Real.toString (Real.fromInt value / 1000.0) ^ "s")
      val fields =
        [ Option.map (fn value => "size " ^ Int.toString value)
            (lookup_stat "size" stats),
          msec,
          Option.map (fn value =>
            "candidates generated " ^ Int.toString value)
            (lookup_stat "candidates_generated" stats),
          Option.map (fn value =>
            "assumptions satisfied " ^ Int.toString value)
            (lookup_stat "assumption_satisfied" stats),
          Option.map (fn value =>
            "conclusions evaluated " ^ Int.toString value)
            (lookup_stat "conclusion_evaluated" stats) ]
      val present = List.mapPartial (fn value => value) fields
    in
      if null present then "" else ", " ^ String.concatWith ", " present
    end

  fun format_term term =
    let
      fun quotient_argument candidate =
        let val (head, arguments) = HolKernel.strip_comb candidate
        in
          case Lib.total Term.dest_thy_const head of
              SOME {Thy = "refute", Name = "Quot", ...} =>
                if length arguments = 1 then SOME (hd arguments) else NONE
            | _ => NONE
        end
      fun delimit value =
        if Feedback.get_tracefn "PP.avoid_unicode" () = 1 then
          "<<" ^ value ^ ">>"
        else
          "«" ^ value ^ "»"
      fun replace_quotients candidate index replacements =
        case quotient_argument candidate of
            SOME argument =>
              let
                val name = "refute$quotdisplay$" ^ Int.toString index ^
                  "$value"
                val placeholder = Term.variant (Term.all_vars term)
                  (Term.mk_var (name, Term.type_of candidate))
              in
                (placeholder, index + 1,
                 (placeholder, delimit (format_term argument)) :: replacements)
              end
          | NONE =>
              if Term.is_abs candidate then
                let
                  val (variable, body) = Term.dest_abs candidate
                  val (body, next, replacements) =
                    replace_quotients body index replacements
                in
                  (Term.mk_abs (variable, body), next, replacements)
                end
              else if Term.is_comb candidate then
                let
                  val (function, argument) = Term.dest_comb candidate
                  val (function, next, replacements) =
                    replace_quotients function index replacements
                  val (argument, next, replacements) =
                    replace_quotients argument next replacements
                in
                  (Term.mk_comb (function, argument), next, replacements)
                end
              else
                (candidate, index, replacements)
      fun replace_all needle replacement source =
        let
          val needle_length = size needle
          val source_length = size source
          fun scan index parts =
            if index >= source_length then String.concat (rev parts)
            else if index + needle_length <= source_length andalso
                    String.substring (source, index, needle_length) = needle
            then scan (index + needle_length) (replacement :: parts)
            else scan (index + 1)
              (String.substring (source, index, 1) :: parts)
        in
          scan 0 []
        end
      val (printable, _, replacements) = replace_quotients term 0 []
      (* A placeholder must print identically in isolation and in context.
         Suppressing free-variable annotations also prevents line wrapping
         from splitting an annotation away from its marker. *)
      val string = Lib.with_flag (Globals.show_types, false)
        Parse.term_to_string printable
      val length = size string
      fun clean index parts =
        if index >= length then String.concat (rev parts)
        else if index + 1 < length andalso
                String.substring (string, index, 2) = "$?" then
          clean (index + 2) ("?" :: parts)
        else if index + 3 < length andalso
                String.substring (string, index, 4) = "$..." then
          clean (index + 4) ("..." :: parts)
        else
          clean (index + 1)
            (String.substring (string, index, 1) :: parts)
    in
      List.foldl (fn ((placeholder, replacement), result) =>
        replace_all
          (Lib.with_flag (Globals.show_types, false)
             Parse.term_to_string placeholder)
          replacement result) (clean 0 []) replacements
    end

  fun format_bindings bindings =
    String.concatWith "\n" (map (fn (name, value) =>
      "  " ^ format_term name ^ " = " ^ format_term value) bindings)

  fun boolean_value_for_display term =
    if Term.type_of term <> Type.bool then NONE
    else
      let
        val theorem =
          simpLib.SIMP_CONV (BasicProvers.srw_ss ()) [] term
        val value = #2 (boolSyntax.dest_eq (Thm.concl theorem))
      in
        if Term.aconv value boolSyntax.T orelse
           Term.aconv value boolSyntax.F then SOME value
        else NONE
      end
      handle Interrupt => raise Interrupt | _ => NONE

  fun format_bool_function value =
    case Lib.total Type.dom_rng (Term.type_of value) of
        SOME (domain, range) =>
          if domain = Type.bool andalso range = Type.bool then
            let
              fun at argument = boolean_value_for_display
                (Term.mk_comb (value, argument))
            in
              case (at boolSyntax.F, at boolSyntax.T) of
                  (SOME at_false, SOME at_true) =>
                    let val arrow =
                      if Feedback.get_tracefn "PP.avoid_unicode" () = 1 then
                        "|->"
                      else
                        "↦"
                    in
                      SOME ("{F " ^ arrow ^ " " ^ format_term at_false ^
                        ", T " ^ arrow ^ " " ^ format_term at_true ^ "}")
                    end
                | _ => NONE
            end
          else NONE
      | NONE => NONE

  fun format_kodkod_bindings bindings =
    String.concatWith "\n" (map (fn (name, value) =>
      "  " ^ format_term name ^ " = " ^
      Option.getOpt (format_bool_function value, format_term value)) bindings)

  fun format_evals evals =
    String.concatWith "\n" (map (fn (term, value) =>
      "  " ^ format_term term ^ " = " ^ format_term
        (Option.getOpt (boolean_value_for_display value, value))) evals)

  fun format_reasons title reasons =
    if null reasons then "" else
      "\n" ^ title ^ "\n" ^ String.concatWith "\n"
        (map (fn reason => "  " ^ reason) reasons)

  fun type_name ty =
    let val printed = Parse.type_to_string ty
    in
      if String.isPrefix ":" printed then
        String.extract (printed, 1, NONE)
      else
        printed
    end

  fun unbox_display_type ty =
    if Type.is_vartype ty then ty
    else
      let val {Thy, Tyop, Args} = Type.dest_thy_type ty
      in
        if Thy = "refute" andalso Tyop = "funbox" then
          Type.-->(unbox_display_type (List.nth (Args, 0)),
            unbox_display_type (List.nth (Args, 1)))
        else if Thy = "refute" andalso Tyop = "pairbox" then
          pairSyntax.mk_prod
            (unbox_display_type (List.nth (Args, 0)),
             unbox_display_type (List.nth (Args, 1)))
        else
          Type.mk_thy_type {Thy = Thy, Tyop = Tyop,
            Args = map unbox_display_type Args}
      end

  fun is_boxed_type ty =
    case Lib.total Type.dest_thy_type ty of
        SOME {Thy = "refute", Tyop = "funbox", ...} => true
      | SOME {Thy = "refute", Tyop = "pairbox", ...} => true
      | _ => false

  fun iterator_scope_name ty =
    if Type.is_vartype ty then
      let
        val name = Type.dest_vartype ty
        val lfp_prefix = "'refute$lfpit$"
        val gfp_prefix = "'refute$gfpit$"
        fun after prefix = String.extract (name, size prefix, NONE)
      in
        if String.isPrefix lfp_prefix name then SOME (after lfp_prefix)
        else if String.isPrefix gfp_prefix name then SOME (after gfp_prefix)
        else NONE
      end
    else NONE

  fun format_scope_assignment (ty, card) =
    case iterator_scope_name ty of
        SOME predicate =>
          "iter " ^ predicate ^ " = " ^ Int.toString (Int.max (0, card - 1))
      | NONE =>
          (case Lib.total Type.dest_thy_type ty of
               SOME {Thy = "refute", Tyop = "bisim_iterator", ...} =>
                 "bisim_depth = " ^ Int.toString (card - 1)
             | _ =>
                 "card " ^ type_name (unbox_display_type ty) ^ " = " ^
                 Int.toString card)

  fun format_scope NONE = ""
    | format_scope (SOME assignments) =
        "\nScope: " ^ String.concatWith ", "
          (map format_scope_assignment assignments)

  fun format_named_terms title entries =
    if null entries then "" else
      "\n" ^ title ^ ":\n" ^ String.concatWith "\n"
        (map (fn (name, value) =>
          "  " ^ name ^ " = " ^ format_term value) entries)

  fun format_types types =
    if null types then "" else
      "\nTypes:\n" ^ String.concatWith "\n" (map
        (fn (ty, values, complete) =>
          "  " ^ type_name (unbox_display_type ty) ^
          (if is_boxed_type ty then " [boxed]" else "") ^ " = {" ^
          String.concatWith ", " (map format_term values) ^
          (if complete then "" else
             if null values then "..." else ", ...") ^ "}") types)

  fun format_model (mf : mf_config) NONE = ""
    | format_model mf (SOME ({skolems, consts, types} : model_report)) =
        (if #show_types mf then format_types types else "") ^
        (if #show_skolems mf then
           format_named_terms "Skolem constants" skolems
         else "") ^
        (if #show_consts mf andalso not (null consts) then
           "\nConstants:\n" ^ String.concatWith "\n"
             (map (fn (name, operator, value) =>
               "  " ^ format_term name ^ " " ^ operator ^ " " ^
               format_term value) consts)
         else "")

  fun format_witness noun (mf : mf_config) (cex : counterexample) =
    let
      val {backend, substrate, certainty, bindings, evals, cert, scope,
           model, stats} = cex
      val candidate_word =
        case certainty of Potential _ => "candidate " | _ => ""
      val header = "Refute found a " ^ candidate_word ^ noun ^
        " (backend: " ^ backend ^ ", substrate: " ^ substrate ^
        format_stats stats ^ "):"
      val scope_text =
        if substrate = "kodkod" then format_scope scope else ""
      val binding_text =
        if null bindings then ""
        else "\n" ^
          (if substrate = "kodkod" then format_kodkod_bindings bindings
           else format_bindings bindings)
      val eval_text =
        if null evals then "" else "\nEvaluated terms:\n" ^ format_evals evals
      val model_text = format_model mf model
      val cert_text =
        case (certainty, cert) of
            (Genuine, NONE) => "\nCertification: uncertified"
          | (_, NONE) => ""
          | (_, SOME theorem) =>
              "\nCertified: " ^ Parse.thm_to_string theorem
      val certainty_text =
        case certainty of
            Genuine => ""
          | QuasiGenuine reasons => format_reasons "Quasi-genuine:" reasons
          | Potential reasons =>
              format_reasons "Why this candidate is unconfirmed:" reasons ^
              "\n…continuing search for a confirmed " ^ noun
    in
      header ^ scope_text ^ binding_text ^ eval_text ^ model_text ^
      cert_text ^ certainty_text
    end

  fun format_outcome (cfg : config) result =
    let
      val body =
        case result of
            Counterexample cexs =>
              String.concatWith "\n\n"
                (map (format_witness "counterexample" (#mf cfg)) cexs)
          | NoCounterexample =>
              "Refute searched the whole space: no counterexample is " ^
              "possible"
          | Model models =>
              String.concatWith "\n\n"
                (map (format_witness "model" (#mf cfg)) models)
          | NoModel =>
              "Refute searched the whole space: no model is possible"
          | Unknown reasons =>
              "Refute search was inconclusive" ^
              format_reasons "Reasons:" reasons
    in
      body ^ #tag cfg
    end

  fun report_outcome (cfg : config) result =
    Private.say 1 (format_outcome cfg result ^ "\n")

  fun certainty_rank Genuine = 3
    | certainty_rank (QuasiGenuine _) = 2
    | certainty_rank (Potential _) = 1

  fun best_certainty [] = NONE
    | best_certainty (cex :: cexs) =
        SOME (#certainty (List.foldl (fn (candidate, best) =>
          if certainty_rank (#certainty candidate) >
             certainty_rank (#certainty best)
          then candidate
          else best) cex cexs))

  fun decisive cfg ceiling (Counterexample cexs) =
        not (null cexs) andalso
        (#abort_potential cfg orelse
         (case best_certainty cexs of
              SOME certainty =>
                certainty_rank certainty >= certainty_rank ceiling
            | NONE => false))
    (* Totality outranks an in-flight Potential candidate.  A Genuine
       counterexample racing this result would expose a soundness bug in one
       of the backends; the ordinary first decisive result still wins. *)
    | decisive _ _ NoCounterexample = true
    (* Model search is auxiliary when it is selected alongside refutation.
       In particular, it must not preempt a QC counterexample or proof of
       whole-space exhaustion. *)
    | decisive _ _ (Model _) = false
    | decisive _ _ NoModel = false
    | decisive _ _ _ = false

  fun best_counterexample_result jobs =
    let
      fun candidate (backend, result_ref) =
        case !result_ref of
            SOME (Counterexample cexs) =>
              Option.map (fn certainty =>
                (backend, cexs, certainty_rank certainty))
                (best_certainty cexs)
          | _ => NONE
      fun better ((backend, _, rank), (best_backend, _, best_rank)) =
        rank > best_rank orelse
        (rank = best_rank andalso
         #weight backend < #weight best_backend)
      fun choose (candidate, NONE) = SOME candidate
        | choose (candidate, SOME best) =
            SOME (if better (candidate, best) then candidate else best)
    in
      case List.foldl choose NONE (List.mapPartial candidate jobs) of
          SOME (_, cexs, _) => SOME (Counterexample cexs)
        | NONE => NONE
    end

  fun has_no_counterexample jobs =
    List.exists (fn (_, result_ref) =>
      case !result_ref of
          SOME NoCounterexample => true
        | _ => false) jobs

  fun best_model_result jobs =
    let
      fun candidate (backend, result_ref) =
        case !result_ref of
            SOME (Model models) =>
              Option.map (fn certainty =>
                (backend, models, certainty_rank certainty))
                (best_certainty models)
          | _ => NONE
      fun better ((backend, _, rank), (best_backend, _, best_rank)) =
        rank > best_rank orelse
        (rank = best_rank andalso
         #weight backend < #weight best_backend)
      fun choose (candidate, NONE) = SOME candidate
        | choose (candidate, SOME best) =
            SOME (if better (candidate, best) then candidate else best)
    in
      case List.foldl choose NONE (List.mapPartial candidate jobs) of
          SOME (_, models, _) => SOME (Model models)
        | NONE => NONE
    end

  fun has_no_model jobs =
    List.exists (fn (_, result_ref) =>
      case !result_ref of SOME NoModel => true | _ => false) jobs

  fun exception_reason e = Feedback.exn_to_string e

  fun no_generator_reason (ty, reason) =
    "no generator for " ^ Parse.type_to_string ty ^ ": " ^ reason

  type search_context =
    { started : Time.time,
      deadline : Time.time,
      expired : unit -> bool,
      remaining : unit -> Time.time }

  fun make_search_context timeout : search_context =
    let
      val started = Time.now ()
      val budget =
        if timeout <= 0.0 then Time.zeroTime else Time.fromReal timeout
      val deadline = started + budget
      fun expired () = Time.now () >= deadline
      fun remaining () =
        let val now = Time.now ()
        in if now >= deadline then Time.zeroTime else Time.- (deadline, now)
        end
    in
      {started = started, deadline = deadline,
       expired = expired, remaining = remaining}
    end

  val active_refute_context : unit ref Thread_Data.var = Thread_Data.var ()
  val active_search_context : search_context Thread_Data.var =
    Thread_Data.var ()
  val active_backend_result : outcome option ref Thread_Data.var =
    Thread_Data.var ()

  fun publish_found make_result found =
    if null found then ()
    else
      case Thread_Data.get active_backend_result of
          NONE => ()
        | SOME published =>
            let
              fun rank values =
                Option.getOpt (Option.map certainty_rank
                  (best_certainty values), 0)
              val replace =
                case (!published, make_result found) of
                    (SOME (Counterexample old), Counterexample _) =>
                      rank found > rank old orelse
                      (rank found = rank old andalso
                       length found >= length old)
                  | (SOME (Model old), Model _) =>
                      rank found > rank old orelse
                      (rank found = rank old andalso
                       length found >= length old)
                  | _ => true
            in
              if replace then published := SOME (make_result found)
              else ()
            end

  fun publish_counterexamples cexs = publish_found Counterexample cexs
  fun publish_models models = publish_found Model models

  fun search_context_for (cfg : config) =
    case Thread_Data.get active_search_context of
        SOME context => context
      | NONE => make_search_context (#timeout cfg)

  fun with_search_context (cfg : config) action argument =
    case Thread_Data.get active_search_context of
        SOME _ => action argument
      | NONE => Thread_Data.setmp active_search_context
          (SOME (make_search_context (#timeout cfg))) action argument

  fun search_expired cfg = #expired (search_context_for cfg) ()

  datatype admission =
      Eligible of backend_registration
    | Excluded of backend_registration
    | AdmissionTimeout of string
    | AdmissionError of string * exn

  fun run_backend context search_context (cfg : config) ceiling forms
        (backend, result_ref) =
    Thread_Data.setmp active_refute_context context (fn () =>
    Thread_Data.setmp active_search_context (SOME search_context) (fn () =>
    let
      val name = #name backend
      val instances = instances_for_form (#input backend) forms
      val _ = Private.say 2
        ("Refute backend started (weight " ^ Int.toString (#weight backend) ^
         "): " ^ name ^ "\n")
      fun timed_run () = Timeout.apply (#remaining search_context ())
        (#run backend cfg) instances
      val raw_result = Thread_Data.setmp active_backend_result
        (SOME result_ref) (fn () =>
          timed_run ()
          handle Timeout.TIMEOUT _ =>
            (case !result_ref of
                 SOME (published as Counterexample _) => published
               | SOME (published as Model _) => published
               | _ => Unknown [name ^ " timed out"])
               | Refute_Gen.NoGenerator pair =>
                   Unknown [name ^ ": " ^ no_generator_reason pair]
               | Interrupt => raise Interrupt
               | e => Unknown [name ^ ": " ^ exception_reason e]) ()
      val result = preserve_polymorphic_bounds backend forms instances
        raw_result
      val _ = result_ref := SOME result
    in
      if decisive cfg ceiling result then SOME result else NONE
    end) ()) ()

  fun unknown_results jobs =
    let
      fun one (backend, result_ref) =
        case !result_ref of
            SOME (Unknown reasons) =>
              map (fn reason => #name backend ^ ": " ^ reason) reasons
          | SOME _ => []
          | NONE => [#name backend ^ " was interrupted"]
    in
      List.concat (map one jobs)
    end

  fun instance_gate_reasons instances =
    let
      fun add_reason (reason, reasons) =
        if List.exists (fn old => old = reason) reasons then reasons
        else reasons @ [reason]
      fun add_instance (instance : instance, reasons) =
        case #qc_gate instance of
            NONE => reasons
          | SOME more => List.foldl add_reason reasons more
    in
      List.foldl add_instance [] instances
    end

  fun instance_is_executable (instance : instance) =
    not (Option.isSome (#qc_gate instance))

  fun instances_are_executable instances =
    List.all instance_is_executable instances

  fun reachable_certainty cfg instances registrations =
    let
      fun higher (registration : backend_registration, best) =
        let
          val ceiling = #certainty_ceiling registration cfg instances
        in
          if certainty_rank ceiling > certainty_rank best then ceiling
          else best
        end
    in
      List.foldl higher (Potential ["no selected backend"]) registrations
    end

  fun meets_requirement cfg executable (backend : backend) instances =
    case #requires backend of
        AnyGoal => true
      | ExecutableGoal => executable
      | ExecutableGoalUnless predicate =>
          executable orelse predicate cfg instances

  fun admit_backend context search_context (cfg : config) forms registration =
    Thread_Data.setmp active_refute_context context (fn () =>
    Thread_Data.setmp active_search_context (SOME search_context) (fn () =>
      let
        val backend = #backend registration
        val name = #name backend
        fun attempt () =
          if not (#configured backend ()) then
            (Excluded registration, false)
          else
            let
              val instances = instances_for_form (#input backend) forms
            in
              if meets_requirement cfg
                   (instances_are_executable instances) backend instances
              then (Eligible registration, true)
              else (Excluded registration, true)
            end
      in
        Timeout.apply (#remaining search_context ()) attempt ()
        handle Timeout.TIMEOUT _ => (AdmissionTimeout name, true)
             | Interrupt => raise Interrupt
             | error => (AdmissionError (name, error), true)
      end) ()) ()

  fun certainty_expectation Genuine = ExpectGenuine
    | certainty_expectation (QuasiGenuine _) = ExpectQuasiGenuine
    | certainty_expectation (Potential _) = ExpectPotential

  fun actual_name (Counterexample cexs) =
        (case best_certainty cexs of
             SOME certainty => Private.expectation_to_string
               (certainty_expectation certainty)
           | NONE => "ExpectCex")
    | actual_name NoCounterexample = "ExpectNone"
    | actual_name (Model _) = "ExpectModel"
    | actual_name NoModel = "ExpectNoModel"
    | actual_name (Unknown _) = "ExpectUnknown"

  fun expectation_holds NoExpectation _ = true
    | expectation_holds ExpectNone NoCounterexample = true
    | expectation_holds ExpectUnknown (Unknown _) = true
    | expectation_holds ExpectCex (Counterexample (_ :: _)) = true
    | expectation_holds ExpectModel (Model (_ :: _)) = true
    | expectation_holds ExpectNoModel NoModel = true
    | expectation_holds expectation (Counterexample cexs) =
        (case best_certainty cexs of
             SOME certainty =>
               expectation = certainty_expectation certainty
           | NONE => false)
    | expectation_holds expectation (Model models) =
        (case best_certainty models of
             SOME certainty =>
               expectation = certainty_expectation certainty
           | NONE => false)
    | expectation_holds _ _ = false

  fun check_expect cfg result =
    if expectation_holds (#expect cfg) result then ()
    else raise Feedback.mk_HOL_ERR "Refute" "expect"
      ("expected " ^ Private.expectation_to_string (#expect cfg) ^
       ", got " ^ actual_name result ^ "\n" ^
       format_outcome cfg result)

  fun refute_problem_unquiet (cfg : config) (problem : problem) =
    let
      val search_context = make_search_context (#timeout cfg)
      fun finish result =
        (report_outcome cfg result; check_expect cfg result; result)
      fun execute () =
        let
          val (candidates, unknown) =
            resolve_backend_registrations (#backends cfg)
        in
          if not (null unknown) then
            Unknown (map (fn name => "unknown requested backend: " ^ name)
              unknown)
          else
            let
          val forms = Timeout.apply (#remaining search_context ())
            (preprocess_forms cfg) problem
          fun registration_instances registration =
            instances_for_form (#input (#backend registration)) forms
          val context = Thread_Data.get active_refute_context
          fun admit registration =
            admit_backend context search_context cfg forms registration
          (* Admission may compile and park a complete smart-generator test.
             In the default profile every registration gets its own local
             worker, independently of the process-global thread count. *)
          val admissions =
            if #sequential cfg then map admit candidates
            else
              case candidates of
                  [] => []
                | _ => ParList.map_with_workers (length candidates) admit
                    candidates
          val selected = List.mapPartial (fn (admission, _) =>
            case admission of Eligible registration => SOME registration
                            | _ => NONE) admissions
          val configured = List.exists #2 admissions
          fun add_reason (reason, reasons) =
            if List.exists (fn old => old = reason) reasons then reasons
            else reasons @ [reason]
          fun add_reasons (more, reasons) =
            List.foldl add_reason reasons more
          fun admission_reasons ((admission, _), reasons) =
            case admission of
                Excluded registration =>
                  add_reasons
                    (instance_gate_reasons
                       (registration_instances registration), reasons)
              | AdmissionTimeout name =>
                  add_reason (name ^ " admission timed out", reasons)
              | _ => reasons
          val excluded_reasons =
            List.foldl admission_reasons [] admissions
          fun admission_error (admission, _) =
            case admission of
                AdmissionError (name, error) =>
                  SOME (name ^ ": " ^ exception_reason error)
              | _ => NONE
          val admission_errors =
            List.mapPartial admission_error admissions
          val _ = List.app (fn reason => Private.say 2
            ("Refute: QC backends excluded: " ^ reason ^ "\n"))
            excluded_reasons
        in
          if not (null admission_errors) then
            Unknown (admission_errors @ excluded_reasons @
              (if #expired search_context () then ["search timed out"]
               else []))
          else if not configured then Unknown ["no configured backend"]
          else if #expired search_context () then
            Unknown (excluded_reasons @ ["search timed out"])
          else if null selected then Unknown excluded_reasons
          else
            let
              fun higher (registration : backend_registration, best) =
                let
                  val candidate = #certainty_ceiling registration cfg
                    (registration_instances registration)
                in
                  if certainty_rank candidate > certainty_rank best then
                    candidate
                  else best
                end
              val ceiling = List.foldl higher
                (Potential ["no selected backend"]) selected
              val jobs = map (fn registration =>
                (#backend registration, ref NONE : outcome option ref))
                selected
              fun noncounterexample_result () =
                if has_no_counterexample jobs then NoCounterexample
                else
                  case best_model_result jobs of
                      SOME result => result
                    | NONE =>
                        if has_no_model jobs then NoModel
                        else
                          let
                            val reasons = excluded_reasons @
                              unknown_results jobs @
                              (if #expired search_context () then
                                 ["search timed out"]
                               else [])
                          in
                            if null reasons then
                              Unknown
                                ["all selected backends returned no result"]
                            else Unknown reasons
                          end
              val winner =
                if #sequential cfg then
                  ParList.get_first
                    (run_backend (Thread_Data.get active_refute_context)
                      search_context cfg ceiling forms) jobs
                else
                  ParList.get_some_with_workers (length jobs)
                    (run_backend (Thread_Data.get active_refute_context)
                      search_context cfg ceiling forms) jobs
            in
              case winner of
                  SOME result => result
                | NONE =>
                    (case best_counterexample_result jobs of
                         SOME result => result
                       | NONE => noncounterexample_result ())
            end
            end
        end
      fun attempt () =
        execute ()
        handle Refute_Gen.NoGenerator pair =>
          Unknown [no_generator_reason pair]
             | InstantiateError message => Unknown [message]
             | Timeout.TIMEOUT _ => Unknown ["search timed out"]
             | Interrupt => raise Interrupt
             | e => Unknown [exception_reason e]
      val result = Thread_Data.setmp active_search_context
        (SOME search_context)
        (Portable.finally release_run_resources attempt) ()
    in
      finish result
    end

  val quiet_mutex = Mutex.mutex ()

  fun refute_problem (cfg : config) problem =
    let
      fun run () =
        if not (#quiet cfg) then refute_problem_unquiet cfg problem
        else
          Feedback.with_traces [("Refute", 0)]
            (Feedback.quiet_messages
              (Feedback.quiet_warnings
                (refute_problem_unquiet cfg))) problem
      (* Output settings in Feedback are process-global.  A callback may
         re-enter Refute from a backend worker, but it must inherit the
         enclosing output scope rather than racing to change those settings. *)
      fun in_context () =
        Thread_Data.setmp active_refute_context (SOME (ref ())) run ()
    in
      case Thread_Data.get active_refute_context of
          (* The surrounding call already owns the global output scope, but
             a reentrant request must still apply its own [quiet] setting. *)
          SOME _ => run ()
        | NONE =>
            Multithreading.synchronized "Refute quiet output" quiet_mutex
              in_context
    end

  fun refute cfg tm =
    refute_problem cfg {goal = tm, assumptions = [], evals = []}
end
