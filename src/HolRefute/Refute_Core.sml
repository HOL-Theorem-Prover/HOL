structure Refute_Core = struct
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

  datatype outcome =
      Counterexample of counterexample list
    | NoCounterexample
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
    | ExpectGenuine
    | ExpectQuasiGenuine
    | ExpectPotential

  datatype substrate_choice = Auto | Compute | Cv | NativeSML

  type qc_config =
    { size : int,
      iterations : int,
      depth : int,
      finite_types : bool,
      finite_type_size : int,
      default_type : hol_type list,
      substrate : substrate_choice,
      allow_function_inversion : bool,
      use_subtype : bool,
      seed : int option,
      smart_quantifier : bool,
      optimise_equality : bool }

  type mf_config =
    { card : (hol_type option * int list) list,
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
      need : term list option }

  type config =
    { timeout : real,
      backends : string list option,
      sequential : bool,
      genuine_only : bool,
      abort_potential : bool,
      no_assms : bool,
      evals : term list,
      expect : expectation,
      max_counterexamples : int,
      tag : string,
      qc : qc_config,
      mf : mf_config }

  type instance =
    { original : term,
      goal : term,
      qc_gate : string list option,
      evals : term list,
      card : int,
      size_matters : bool }

  datatype requirement = ExecutableGoal | AnyGoal
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
      iterations = 100,
      depth = 10,
      finite_types = true,
      finite_type_size = 3,
      default_type = [``:num``],
      substrate = Auto,
      allow_function_inversion = false,
      use_subtype = false,
      seed = NONE,
      smart_quantifier = true,
      optimise_equality = true }

  val default_mf_config : mf_config =
    { card = [(NONE, List.tabulate (10, fn n => n + 1))],
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
      star_linear_preds = false,
      iter = [(NONE, [0])],
      bisim_depth = [~1],
      finitize = [(NONE, NONE)],
      whack = [],
      need = NONE }

  val default_config : config =
    { timeout = 30.0,
      backends = NONE,
      sequential = false,
      genuine_only = false,
      abort_potential = false,
      no_assms = false,
      evals = [],
      expect = NoExpectation,
      max_counterexamples = 1,
      tag = "",
      qc = default_qc_config,
      mf = default_mf_config }

  val the_config = ref default_config

  fun map_qc f (cfg : config) =
    let
      val {timeout, backends, sequential, genuine_only, abort_potential,
           no_assms, evals, expect, max_counterexamples, tag, qc, mf} = cfg
    in
      { timeout = timeout,
        backends = backends,
        sequential = sequential,
        genuine_only = genuine_only,
        abort_potential = abort_potential,
        no_assms = no_assms,
        evals = evals,
        expect = expect,
        max_counterexamples = max_counterexamples,
        tag = tag,
        qc = f qc,
        mf = mf }
    end

  fun map_mf f (cfg : config) =
    let
      val {timeout, backends, sequential, genuine_only, abort_potential,
           no_assms, evals, expect, max_counterexamples, tag, qc, mf} = cfg
    in
      { timeout = timeout,
        backends = backends,
        sequential = sequential,
        genuine_only = genuine_only,
        abort_potential = abort_potential,
        no_assms = no_assms,
        evals = evals,
        expect = expect,
        max_counterexamples = max_counterexamples,
        tag = tag,
        qc = qc,
        mf = f mf }
    end

  fun upd_timeout value (cfg : config) =
    { timeout = value,
      backends = #backends cfg,
      sequential = #sequential cfg,
      genuine_only = #genuine_only cfg,
      abort_potential = #abort_potential cfg,
      no_assms = #no_assms cfg,
      evals = #evals cfg,
      expect = #expect cfg,
      max_counterexamples = #max_counterexamples cfg,
      tag = #tag cfg,
      qc = #qc cfg,
      mf = #mf cfg }

  fun upd_backends value (cfg : config) =
    { timeout = #timeout cfg,
      backends = value,
      sequential = #sequential cfg,
      genuine_only = #genuine_only cfg,
      abort_potential = #abort_potential cfg,
      no_assms = #no_assms cfg,
      evals = #evals cfg,
      expect = #expect cfg,
      max_counterexamples = #max_counterexamples cfg,
      tag = #tag cfg,
      qc = #qc cfg,
      mf = #mf cfg }

  fun upd_sequential value (cfg : config) =
    { timeout = #timeout cfg,
      backends = #backends cfg,
      sequential = value,
      genuine_only = #genuine_only cfg,
      abort_potential = #abort_potential cfg,
      no_assms = #no_assms cfg,
      evals = #evals cfg,
      expect = #expect cfg,
      max_counterexamples = #max_counterexamples cfg,
      tag = #tag cfg,
      qc = #qc cfg,
      mf = #mf cfg }

  fun upd_genuine_only value (cfg : config) =
    { timeout = #timeout cfg,
      backends = #backends cfg,
      sequential = #sequential cfg,
      genuine_only = value,
      abort_potential = #abort_potential cfg,
      no_assms = #no_assms cfg,
      evals = #evals cfg,
      expect = #expect cfg,
      max_counterexamples = #max_counterexamples cfg,
      tag = #tag cfg,
      qc = #qc cfg,
      mf = #mf cfg }

  fun upd_abort_potential value (cfg : config) =
    { timeout = #timeout cfg,
      backends = #backends cfg,
      sequential = #sequential cfg,
      genuine_only = #genuine_only cfg,
      abort_potential = value,
      no_assms = #no_assms cfg,
      evals = #evals cfg,
      expect = #expect cfg,
      max_counterexamples = #max_counterexamples cfg,
      tag = #tag cfg,
      qc = #qc cfg,
      mf = #mf cfg }

  fun upd_no_assms value (cfg : config) =
    { timeout = #timeout cfg,
      backends = #backends cfg,
      sequential = #sequential cfg,
      genuine_only = #genuine_only cfg,
      abort_potential = #abort_potential cfg,
      no_assms = value,
      evals = #evals cfg,
      expect = #expect cfg,
      max_counterexamples = #max_counterexamples cfg,
      tag = #tag cfg,
      qc = #qc cfg,
      mf = #mf cfg }

  fun upd_evals value (cfg : config) =
    { timeout = #timeout cfg,
      backends = #backends cfg,
      sequential = #sequential cfg,
      genuine_only = #genuine_only cfg,
      abort_potential = #abort_potential cfg,
      no_assms = #no_assms cfg,
      evals = value,
      expect = #expect cfg,
      max_counterexamples = #max_counterexamples cfg,
      tag = #tag cfg,
      qc = #qc cfg,
      mf = #mf cfg }

  fun upd_expect value (cfg : config) =
    { timeout = #timeout cfg,
      backends = #backends cfg,
      sequential = #sequential cfg,
      genuine_only = #genuine_only cfg,
      abort_potential = #abort_potential cfg,
      no_assms = #no_assms cfg,
      evals = #evals cfg,
      expect = value,
      max_counterexamples = #max_counterexamples cfg,
      tag = #tag cfg,
      qc = #qc cfg,
      mf = #mf cfg }

  fun upd_max_counterexamples value (cfg : config) =
    { timeout = #timeout cfg,
      backends = #backends cfg,
      sequential = #sequential cfg,
      genuine_only = #genuine_only cfg,
      abort_potential = #abort_potential cfg,
      no_assms = #no_assms cfg,
      evals = #evals cfg,
      expect = #expect cfg,
      max_counterexamples = value,
      tag = #tag cfg,
      qc = #qc cfg,
      mf = #mf cfg }

  fun upd_tag value (cfg : config) =
    { timeout = #timeout cfg,
      backends = #backends cfg,
      sequential = #sequential cfg,
      genuine_only = #genuine_only cfg,
      abort_potential = #abort_potential cfg,
      no_assms = #no_assms cfg,
      evals = #evals cfg,
      expect = #expect cfg,
      max_counterexamples = #max_counterexamples cfg,
      tag = value,
      qc = #qc cfg,
      mf = #mf cfg }

  fun upd_qc value (cfg : config) = map_qc (fn _ => value) cfg

  fun upd_size value = map_qc (fn (qc : qc_config) =>
    { size = value, iterations = #iterations qc, depth = #depth qc,
      finite_types = #finite_types qc,
      finite_type_size = #finite_type_size qc,
      default_type = #default_type qc, substrate = #substrate qc,
      allow_function_inversion = #allow_function_inversion qc,
      use_subtype = #use_subtype qc, seed = #seed qc,
      smart_quantifier = #smart_quantifier qc,
      optimise_equality = #optimise_equality qc })

  fun upd_iterations value = map_qc (fn (qc : qc_config) =>
    { size = #size qc, iterations = value, depth = #depth qc,
      finite_types = #finite_types qc,
      finite_type_size = #finite_type_size qc,
      default_type = #default_type qc, substrate = #substrate qc,
      allow_function_inversion = #allow_function_inversion qc,
      use_subtype = #use_subtype qc, seed = #seed qc,
      smart_quantifier = #smart_quantifier qc,
      optimise_equality = #optimise_equality qc })

  fun upd_depth value = map_qc (fn (qc : qc_config) =>
    { size = #size qc, iterations = #iterations qc, depth = value,
      finite_types = #finite_types qc,
      finite_type_size = #finite_type_size qc,
      default_type = #default_type qc, substrate = #substrate qc,
      allow_function_inversion = #allow_function_inversion qc,
      use_subtype = #use_subtype qc, seed = #seed qc,
      smart_quantifier = #smart_quantifier qc,
      optimise_equality = #optimise_equality qc })

  fun upd_finite_types value = map_qc (fn (qc : qc_config) =>
    { size = #size qc, iterations = #iterations qc, depth = #depth qc,
      finite_types = value, finite_type_size = #finite_type_size qc,
      default_type = #default_type qc, substrate = #substrate qc,
      allow_function_inversion = #allow_function_inversion qc,
      use_subtype = #use_subtype qc, seed = #seed qc,
      smart_quantifier = #smart_quantifier qc,
      optimise_equality = #optimise_equality qc })

  fun upd_finite_type_size value = map_qc (fn (qc : qc_config) =>
    { size = #size qc, iterations = #iterations qc, depth = #depth qc,
      finite_types = #finite_types qc, finite_type_size = value,
      default_type = #default_type qc, substrate = #substrate qc,
      allow_function_inversion = #allow_function_inversion qc,
      use_subtype = #use_subtype qc, seed = #seed qc,
      smart_quantifier = #smart_quantifier qc,
      optimise_equality = #optimise_equality qc })

  fun upd_default_type value = map_qc (fn (qc : qc_config) =>
    { size = #size qc, iterations = #iterations qc, depth = #depth qc,
      finite_types = #finite_types qc,
      finite_type_size = #finite_type_size qc, default_type = value,
      substrate = #substrate qc,
      allow_function_inversion = #allow_function_inversion qc,
      use_subtype = #use_subtype qc, seed = #seed qc,
      smart_quantifier = #smart_quantifier qc,
      optimise_equality = #optimise_equality qc })

  fun upd_substrate value = map_qc (fn (qc : qc_config) =>
    { size = #size qc, iterations = #iterations qc, depth = #depth qc,
      finite_types = #finite_types qc,
      finite_type_size = #finite_type_size qc,
      default_type = #default_type qc, substrate = value,
      allow_function_inversion = #allow_function_inversion qc,
      use_subtype = #use_subtype qc, seed = #seed qc,
      smart_quantifier = #smart_quantifier qc,
      optimise_equality = #optimise_equality qc })

  fun upd_allow_function_inversion value = map_qc (fn (qc : qc_config) =>
    { size = #size qc, iterations = #iterations qc, depth = #depth qc,
      finite_types = #finite_types qc,
      finite_type_size = #finite_type_size qc,
      default_type = #default_type qc, substrate = #substrate qc,
      allow_function_inversion = value, use_subtype = #use_subtype qc,
      seed = #seed qc, smart_quantifier = #smart_quantifier qc,
      optimise_equality = #optimise_equality qc })

  fun upd_use_subtype value = map_qc (fn (qc : qc_config) =>
    { size = #size qc, iterations = #iterations qc, depth = #depth qc,
      finite_types = #finite_types qc,
      finite_type_size = #finite_type_size qc,
      default_type = #default_type qc, substrate = #substrate qc,
      allow_function_inversion = #allow_function_inversion qc,
      use_subtype = value, seed = #seed qc,
      smart_quantifier = #smart_quantifier qc,
      optimise_equality = #optimise_equality qc })

  fun upd_seed value = map_qc (fn (qc : qc_config) =>
    { size = #size qc, iterations = #iterations qc, depth = #depth qc,
      finite_types = #finite_types qc,
      finite_type_size = #finite_type_size qc,
      default_type = #default_type qc, substrate = #substrate qc,
      allow_function_inversion = #allow_function_inversion qc,
      use_subtype = #use_subtype qc, seed = value,
      smart_quantifier = #smart_quantifier qc,
      optimise_equality = #optimise_equality qc })

  fun upd_smart_quantifier value = map_qc (fn (qc : qc_config) =>
    { size = #size qc, iterations = #iterations qc, depth = #depth qc,
      finite_types = #finite_types qc,
      finite_type_size = #finite_type_size qc,
      default_type = #default_type qc, substrate = #substrate qc,
      allow_function_inversion = #allow_function_inversion qc,
      use_subtype = #use_subtype qc, seed = #seed qc,
      smart_quantifier = value,
      optimise_equality = #optimise_equality qc })

  fun upd_optimise_equality value = map_qc (fn (qc : qc_config) =>
    { size = #size qc, iterations = #iterations qc, depth = #depth qc,
      finite_types = #finite_types qc,
      finite_type_size = #finite_type_size qc,
      default_type = #default_type qc, substrate = #substrate qc,
      allow_function_inversion = #allow_function_inversion qc,
      use_subtype = #use_subtype qc, seed = #seed qc,
      smart_quantifier = #smart_quantifier qc, optimise_equality = value })

  fun m4_error field =
    raise Feedback.mk_HOL_ERR "Refute_Core" "validate_mf_config"
      (field ^ ": not implemented until M4")

  fun range_error field explanation =
    raise Feedback.mk_HOL_ERR "Refute_Core" "validate_mf_config"
      (field ^ ": " ^ explanation)

  fun validate_mf_config (mf : mf_config) =
    let
      fun unchanged field same = if same then () else m4_error field
      val _ = if null (#bits mf) orelse
                     List.exists (fn bits => bits < 1 orelse bits > 31)
                       (#bits mf) then
                range_error "bits" "values must lie between 1 and 31"
              else ()
      val _ = unchanged "star_linear_preds"
        (#star_linear_preds mf = #star_linear_preds default_mf_config)
      val _ = (case #iter mf of
                   [(NONE, [0])] => ()
                 | _ => m4_error "iter")
      val _ = unchanged "bisim_depth"
        (#bisim_depth mf = #bisim_depth default_mf_config)
      val _ = if null (#whack mf) then () else m4_error "whack"
      val _ = (case #need mf of NONE => () | SOME _ => m4_error "need")
      val _ = if #max_potential mf > 1 then m4_error "max_potential"
              else ()
      val _ = if #max_genuine mf > 1 then m4_error "max_genuine"
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
    in
      mf
    end

  datatype mf_update =
      MfCard of (hol_type option * int list) list
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

  fun change_mf update (mf : mf_config) =
    { card = (case update of MfCard value => value | _ => #card mf),
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
      need = (case update of MfNeed value => value | _ => #need mf) }

  fun upd_mf value = map_mf (fn _ => validate_mf_config value)

  fun update_mf update = map_mf (validate_mf_config o change_mf update)

  fun upd_card value = update_mf (MfCard value)
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

  fun strip_outer_forall tm = boolSyntax.strip_forall tm

  fun strip_outer_forall_body tm = #2 (strip_outer_forall tm)

  val normal_rewrites =
    [ boolTheory.NOT_EXISTS_THM,
      boolTheory.NOT_FORALL_THM,
      boolTheory.AND_IMP_INTRO,
      boolTheory.FUN_EQ_THM ] @
    Drule.CONJUNCTS boolTheory.PULL_EXISTS @
    Drule.CONJUNCTS boolTheory.PULL_FORALL

  fun normalize tm =
    #2 (boolSyntax.dest_eq (Thm.concl
      (Ho_Rewrite.REWRITE_CONV normal_rewrites tm)))
    handle _ => tm

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
      let
        val (variable, body) = Term.dest_abs tm
      in
        not (Option.isSome
          (Refute_Gen.enumerate (Term.type_of variable))) orelse
        has_unexpanded_binder body
      end
    else if Term.is_comb tm then
      let
        val (left, right) = Term.dest_comb tm
      in
        has_unexpanded_binder left orelse has_unexpanded_binder right
      end
    else
      false

  fun term_constants tm =
    let
      fun collect seen tm =
        if Literal.is_literal tm then
          (* Numeral/string/char literals are closed values that EVAL
             reduces natively; their internal constants (NUMERAL, BIT1,
             STRING, CHR, ...) never leave the evaluator stuck. *)
          seen
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
      val comp_items = computeLib.listItems (!computeLib.the_compset)
      val executable_keys =
        List.foldl (fn ((key, transforms), keys) =>
          if null transforms then keys else Redblackset.add (keys, key))
          (Redblackset.empty
            (Portable.pair_compare (String.compare, String.compare)))
          comp_items
      fun executable_constant constant =
        TypeBase.is_constructor constant orelse
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

  fun clamped_finite_type_size size = Int.max (1, Int.min (6, size))

  fun monomorphic_types qc =
    if #finite_types qc then
      List.tabulate (clamped_finite_type_size (#finite_type_size qc),
        fn index => rf_type (index + 1))
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

  type preprocessed_forms =
    {mono_instances : instance list, poly_original : instance list}

  fun preprocess_forms (cfg : config) (problem : problem) =
    let
      val assumptions =
        if #no_assms cfg then [] else #assumptions problem
      val original_goal = boolSyntax.list_mk_imp (assumptions, #goal problem)
      val input_evals = #evals problem @ #evals cfg
      val types = monomorphic_types (#qc cfg)
      val tyvars = Lib.U
        (map Term.type_vars_in_term (original_goal :: input_evals))
      fun make_instance card theta =
        let
          val original = Term.inst theta original_goal
          val initial_goal = strip_outer_forall_body original
          val normalized_goal =
            strip_outer_forall_body (normalize initial_goal)
          val goal = expand_quantifiers normalized_goal
          val evals = map (Term.inst theta) input_evals
          val evals = add_equation_eval_terms goal evals
          val binders_remain = has_unexpanded_binder goal
          val constants =
            if binders_remain then []
            else nonexecutable_constants (goal :: evals)
          val qc_gate =
            if binders_remain then
              SOME ["not executable: unexpanded binder"]
            else if null constants then NONE
            else SOME ["not executable: " ^ show_constants constants]
        in
          { original = original,
            goal = goal,
            qc_gate = qc_gate,
            evals = evals,
            card = card,
            size_matters = instance_size_matters goal }
        end
      fun monomorphic_instance (card, replacement) =
        make_instance card (map (fn tyvar =>
          {redex = tyvar, residue = replacement}) tyvars)
      val mono_instances =
        if null tyvars then [make_instance 1 []]
        else
          List.map monomorphic_instance
            (ListPair.zip
              (List.tabulate (length types, fn index => index + 1), types))
      (* A monomorphic goal has literally the same backend input in both
         forms.  This is stronger than merely constructing an equivalent
         singleton and keeps the old front-end behaviour exact. *)
      val poly_original =
        if null tyvars then mono_instances else [make_instance 0 []]
    in
      {mono_instances = mono_instances, poly_original = poly_original}
    end

  fun preprocess cfg problem =
    #mono_instances (preprocess_forms cfg problem)

  fun instances_for_form MonoInstances
        ({mono_instances, ...} : preprocessed_forms) = mono_instances
    | instances_for_form PolyOriginal {poly_original, ...} = poly_original

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
      | expectation_to_string ExpectGenuine = "ExpectGenuine"
      | expectation_to_string ExpectQuasiGenuine =
          "ExpectQuasiGenuine"
      | expectation_to_string ExpectPotential = "ExpectPotential"

    fun substrate_to_string Auto = "Auto"
      | substrate_to_string Compute = "Compute"
      | substrate_to_string Cv = "Cv"
      | substrate_to_string NativeSML = "NativeSML"

    fun option_to_string f NONE = "NONE"
      | option_to_string f (SOME x) = "SOME " ^ f x
  end

  fun show_config () =
    let
      val {timeout, backends, sequential, genuine_only, abort_potential,
           no_assms, evals, expect, max_counterexamples, tag, qc, mf} =
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
          "no_assms = " ^ Bool.toString no_assms ^ "\n",
          "evals = " ^ Int.toString (length evals) ^ " terms\n",
          "expect = " ^ Private.expectation_to_string expect ^ "\n",
          "max_counterexamples = " ^ Int.toString max_counterexamples ^ "\n",
          "tag = " ^ tag ^ "\n",
          "size = " ^ Int.toString (#size q) ^ "\n",
          "iterations = " ^ Int.toString (#iterations q) ^ "\n",
          "depth = " ^ Int.toString (#depth q) ^ "\n",
          "finite_types = " ^ Bool.toString (#finite_types q) ^
            "\n",
          "finite_type_size = " ^ Int.toString (#finite_type_size q) ^
            "\n",
          "default_type = " ^ types ^ "\n",
          "substrate = " ^ Private.substrate_to_string (#substrate q) ^
            "\n",
          "allow_function_inversion = " ^
            Bool.toString (#allow_function_inversion q) ^ "\n",
          "use_subtype = " ^ Bool.toString (#use_subtype q) ^
            "\n",
          "seed = " ^ Private.option_to_string Int.toString (#seed q) ^
            "\n",
          "smart_quantifier = " ^
            Bool.toString (#smart_quantifier q) ^ "\n",
          "optimise_equality = " ^
            Bool.toString (#optimise_equality q) ^ "\n",
          "mf.card = " ^ type_ints (#card m) ^ "\n",
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
          "mf.need = " ^ optional_terms (#need m) ^ "\n" ]
    end

  val backend_registry : (string * backend_registration) list ref = ref []

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
    let
      val without_old =
        List.filter (fn (name, _) => name <> #name backend) (!backend_registry)
      val registration =
        {backend = backend, certainty_ceiling = certainty_ceiling}
      val entry = (#name backend, registration)
    in
      backend_registry := insert_backend entry without_old
    end

  fun register_backend backend =
    (* Preserve source compatibility and safety for backends that do not
       opt into a tighter, configuration-sensitive declaration. *)
    register_backend_with_ceiling backend (fn _ => fn _ => Genuine)

  fun registered_backends () = map (#backend o #2) (!backend_registry)

  fun lookup_backend name =
    Option.map (#backend o #2)
      (List.find (fn (registered, _) => registered = name)
        (!backend_registry))

  fun selected_backend_registrations names =
    let
      fun requested (registration : backend_registration) =
        case names of
            NONE => true
          | SOME wanted => List.exists
              (fn name => name = #name (#backend registration)) wanted
    in
      map #2 (List.filter (fn (_, registration) =>
        requested registration andalso
        (#configured (#backend registration)) ()) (!backend_registry))
    end

  fun selected_backends names =
    map #backend (selected_backend_registrations names)

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
          msec ]
      val present = List.mapPartial (fn value => value) fields
    in
      if null present then "" else ", " ^ String.concatWith ", " present
    end

  fun format_term term =
    let
      val string = Parse.term_to_string term
      val length = size string
      fun scan index parts =
        if index >= length then String.concat (rev parts)
        else if index + 1 < length andalso
                String.substring (string, index, 2) = "$?" then
          scan (index + 2) ("?" :: parts)
        else if index + 3 < length andalso
                String.substring (string, index, 4) = "$..." then
          scan (index + 4) ("..." :: parts)
        else
          scan (index + 1)
            (String.substring (string, index, 1) :: parts)
    in
      scan 0 []
    end

  fun format_bindings bindings =
    String.concatWith "\n" (map (fn (name, value) =>
      "  " ^ format_term name ^ " = " ^ format_term value) bindings)

  fun format_evals evals =
    String.concatWith "\n" (map (fn (term, value) =>
      "  " ^ format_term term ^ " = " ^ format_term value) evals)

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

  fun format_scope NONE = ""
    | format_scope (SOME assignments) =
        "\nScope: " ^ String.concatWith ", " (map (fn (ty, card) =>
          "card " ^ type_name (unbox_display_type ty) ^ " = " ^
          Int.toString card) assignments)

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
        (if #show_consts mf then
           format_named_terms "Constants" (map (fn (name, value) =>
             (format_term name, value)) consts)
         else "")

  fun format_counterexample (mf : mf_config) (cex : counterexample) =
    let
      val {backend, substrate, certainty, bindings, evals, cert, scope,
           model, stats} = cex
      val model_word =
        if backend = "kodkod" andalso not (#falsify mf) then "model"
        else "counterexample"
      val header = "Refute found a " ^ model_word ^ " (backend: " ^ backend ^
        ", substrate: " ^ substrate ^ format_stats stats ^ "):"
      val scope_text =
        if substrate = "kodkod" then format_scope scope else ""
      val binding_text =
        if null bindings then "" else "\n" ^ format_bindings bindings
      val eval_text =
        if null evals then "" else "\nEvaluated terms:\n" ^ format_evals evals
      val model_text = format_model mf model
      val cert_text =
        case cert of
            NONE => ""
          | SOME theorem => "\nCertified: " ^ Parse.thm_to_string theorem
      val certainty_text =
        case certainty of
            Genuine => ""
          | QuasiGenuine reasons => format_reasons "Quasi-genuine:" reasons
          | Potential reasons =>
              format_reasons ("Potential " ^ model_word ^ ":") reasons ^
              "\n…continuing search for a genuine " ^ model_word
    in
      header ^ scope_text ^ binding_text ^ eval_text ^ model_text ^
      cert_text ^ certainty_text
    end

  (* "falsify = false" is a model-finder-only setting, so the wording must
     track whether kodkod was selected at all, not whether it was selected
     exclusively; NONE selects every configured backend. *)
  fun backend_selected name (cfg : config) =
    case #backends cfg of
        NONE => true
      | SOME wanted => List.exists (fn chosen => chosen = name) wanted

  fun format_outcome (cfg : config) result =
    let
      val body =
        case result of
            Counterexample cexs =>
              String.concatWith "\n\n"
                (map (format_counterexample (#mf cfg)) cexs)
          | NoCounterexample =>
              "Refute: no " ^
              (if backend_selected "kodkod" cfg andalso
                  not (#falsify (#mf cfg))
               then "model" else "counterexample") ^
              " found within the tested finite bounds"
          | Unknown reasons =>
              "Refute could not determine an answer" ^
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

  fun exception_reason e = Feedback.exn_to_string e

  fun no_generator_reason (ty, reason) =
    "no generator for " ^ Parse.type_to_string ty ^ ": " ^ reason

  fun run_backend (cfg : config) ceiling forms (backend, result_ref) =
    let
      val name = #name backend
      val instances = instances_for_form (#input backend) forms
      val timeout =
        if #timeout cfg <= 0.0 then Time.fromReal 0.0
        else Time.fromReal (#timeout cfg)
      val result =
        (Timeout.apply timeout (#run backend cfg) instances
         handle Timeout.TIMEOUT _ =>
           Unknown [name ^ " timed out"]
              | Refute_Gen.NoGenerator pair =>
                  Unknown [name ^ ": " ^ no_generator_reason pair]
              | Interrupt => raise Interrupt
              | e => Unknown [name ^ ": " ^ exception_reason e])
      val _ = result_ref := SOME result
    in
      if decisive cfg ceiling result then SOME result else NONE
    end

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

  fun meets_requirement executable (backend : backend) =
    case #requires backend of
        AnyGoal => true
      | ExecutableGoal => executable

  fun certainty_expectation Genuine = ExpectGenuine
    | certainty_expectation (QuasiGenuine _) = ExpectQuasiGenuine
    | certainty_expectation (Potential _) = ExpectPotential

  fun actual_name (Counterexample cexs) =
        (case best_certainty cexs of
             SOME certainty => Private.expectation_to_string
               (certainty_expectation certainty)
           | NONE => "ExpectCex")
    | actual_name NoCounterexample = "ExpectNone"
    | actual_name (Unknown _) = "ExpectUnknown"

  fun expectation_holds NoExpectation _ = true
    | expectation_holds ExpectNone NoCounterexample = true
    | expectation_holds ExpectUnknown (Unknown _) = true
    | expectation_holds ExpectCex (Counterexample (_ :: _)) = true
    | expectation_holds expectation (Counterexample cexs) =
        (case best_certainty cexs of
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

  fun refute_problem (cfg : config) (problem : problem) =
    let
      fun finish result =
        (report_outcome cfg result; check_expect cfg result; result)
      fun execute () =
        let
          val configured = selected_backend_registrations (#backends cfg)
          val forms = preprocess_forms cfg problem
          fun registration_instances registration =
            instances_for_form (#input (#backend registration)) forms
          fun registration_is_eligible registration =
            meets_requirement
              (instances_are_executable
                (registration_instances registration))
              (#backend registration)
          val selected = List.filter registration_is_eligible configured
          val excluded =
            List.filter (not o registration_is_eligible) configured
          val excluded_reasons =
            if null excluded then []
            else
              instance_gate_reasons
                (List.concat (map registration_instances excluded))
          val _ = List.app (fn reason => Private.say 2
            ("Refute: QC backends excluded: " ^ reason ^ "\n"))
            excluded_reasons
        in
          if null configured then Unknown ["no configured backend"]
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
              val winner =
                if #sequential cfg then
                  ParList.get_first
                    (run_backend cfg ceiling forms) jobs
                else
                  ParList.get_some
                    (run_backend cfg ceiling forms) jobs
            in
              case winner of
                  SOME result => result
                | NONE =>
                    (case best_counterexample_result jobs of
                         SOME result => result
                       | NONE =>
                           if has_no_counterexample jobs then
                             NoCounterexample
                           else
                             let
                               val reasons =
                                 excluded_reasons @ unknown_results jobs
                             in
                               if null reasons then
                                 Unknown
                                   ["all selected backends returned no result"]
                               else Unknown reasons
                             end)
            end
        end
      val result =
        (execute ()
         handle Refute_Gen.NoGenerator pair =>
           Unknown [no_generator_reason pair]
              | Interrupt => raise Interrupt
              | e => Unknown [exception_reason e])
    in
      finish result
    end

  fun refute cfg tm =
    refute_problem cfg {goal = tm, assumptions = [], evals = []}
end
