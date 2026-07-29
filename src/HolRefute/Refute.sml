structure Refute :> Refute = struct
  type term = Term.term
  type thm = Thm.thm
  type hol_type = Type.hol_type
  type goal = term list * term

  datatype certainty = datatype Refute_Core.certainty
  type counterexample = Refute_Core.counterexample
  type model_report = Refute_Core.model_report
  datatype outcome = datatype Refute_Core.outcome
  datatype expectation = datatype Refute_Core.expectation
  datatype substrate_choice = datatype Refute_Core.substrate_choice
  datatype requirement = datatype Refute_Core.requirement
  datatype goal_form = datatype Refute_Core.goal_form
  type qc_config = Refute_Core.qc_config
  type mf_config = Refute_Core.mf_config
  type config = Refute_Core.config
  type instance = Refute_Core.instance
  type backend = Refute_Core.backend
  type certainty_ceiling = config -> instance list -> certainty
  type substrate = Refute_Eval.substrate
  type custom_gen = Refute_Gen.custom_gen
  type rng = Refute_Gen.rng
  type term_postprocessor = term -> term

  (* Register the built-in backends through this public entry point.
     Refute_QC passes the native extractor explicitly, making both
     implementation units dependencies of [load "Refute"]. *)
  val () = Refute_QC.register_backends ()
  val () = Refute_QC_Narrow.register_backend ()
  val () = Refute_ModelFinder.register_backends ()
  (* Rational Frac encoding and display are part of the default session
     setup; the normalization-faithfulness corpus in selftest.sml keeps
     them honest. *)
  val () = Refute_ModelFinder_Model.register_frac_type_rat ()

  val refute = Refute_Core.refute
  fun refute_def tm = refute (!Refute_Core.the_config) tm

  fun refute_goal cfg (assumptions, goal) =
    Refute_Core.refute_problem cfg
      {goal = goal, assumptions = assumptions, evals = []}

  fun refute_top () = refute_goal (!Refute_Core.the_config)
    (proofManagerLib.top_goal ())

  val try_seed = 42

  fun try_refute cfg (assumptions, goal) =
    let
      val try_config = cfg
        |> Refute_Core.upd_sequential true
        |> Refute_Core.upd_seed (SOME try_seed)
        |> Refute_Core.upd_expect Refute_Core.NoExpectation
        |> Refute_Core.upd_quiet true
      val budget =
        if #timeout try_config <= 0.0 then Time.zeroTime
        else Time.fromReal (#timeout try_config)
      fun run () = Refute_Core.refute_problem try_config
        {goal = goal, assumptions = assumptions, evals = []}
      (* This outer limit is deliberately a whole-call budget.  Threading a
         shared deadline into each backend, as Nitpick does, is a possible
         future refinement that would let backends spend the remainder. *)
      val result = Timeout.apply budget run ()
    in
      case result of
          outcome as Refute_Core.Counterexample (cex :: _) =>
            SOME (#backend cex, outcome)
        | _ => NONE
    end
    handle Timeout.TIMEOUT _ => NONE
         | Time => NONE

  fun qc_only config = Refute_Core.upd_backends
    (SOME (Refute_QC.qc_backend_names ())) config

  (* The option distinguishes the QC-only convenience from an explicitly
     supplied configuration whose [backends = NONE] means the full registry. *)
  fun unused_config NONE = qc_only (!Refute_Core.the_config)
    | unused_config (SOME config) = config

  fun check_unused_assms config named_theorem =
    Refute_Unused.check_unused_assms (unused_config config) named_theorem

  fun find_unused_assms config theory =
    Refute_Unused.find_unused_assms (unused_config config) theory

  fun print_unused_assms config theory =
    Refute_Unused.print_unused_assms (unused_config config) theory

  fun quickcheck tm = refute (qc_only (!Refute_Core.the_config)) tm

  fun nitpick tm = refute
    (Refute_Core.upd_backends (SOME ["kodkod"])
      (!Refute_Core.the_config)) tm

  fun REFUTE_TAC goal =
    case refute_goal (!Refute_Core.the_config) goal of
        Refute_Core.Counterexample cexs =>
          raise Feedback.mk_HOL_ERR "Refute" "REFUTE_TAC"
            (Refute_Core.format_outcome (!Refute_Core.the_config)
              (Refute_Core.Counterexample cexs))
      | _ => Tactical.ALL_TAC goal

  val register_backend = Refute_Core.register_backend
  fun register_backend_with_ceiling backend ceiling =
    Refute_Core.register_backend_with_ceiling backend (fn config =>
      fn instances =>
        case ceiling config instances of
            Genuine => Refute_Core.Genuine
          | QuasiGenuine reasons => Refute_Core.QuasiGenuine reasons
          | Potential reasons => Refute_Core.Potential reasons)
  val register_substrate = Refute_Eval.register_substrate
  val register_generator = Refute_Gen.register_generator
  val register_term_postprocessor =
    Refute_ModelFinder_Model.register_term_postprocessor
  val lookup_term_postprocessor =
    Refute_ModelFinder_Model.lookup_term_postprocessor
  fun register_codatatype registration =
    Refute_ModelFinder_HOL.with_registration_lock (fn () =>
      Refute_ModelFinder_HOL.register_codatatype registration)
  val register_quotient = Refute_ModelFinder_HOL.register_quotient
  val register_typedef = Refute_ModelFinder_HOL.register_typedef
  val register_frac_type = Refute_ModelFinder_HOL.register_frac_type
  val register_frac_type_rat =
    Refute_ModelFinder_Model.register_frac_type_rat
  fun register_ersatz registration =
    Refute_ModelFinder_HOL.with_registration_lock (fn () =>
      Refute_ModelFinder_HOL.register_ersatz registration)
  val abstract_generator = Refute_Gen.abstract_generator

  val export_refute_simp = #export Refute_Core.refute_simp
  val export_refute_psimp = #export Refute_Core.refute_psimp
  val export_refute_unfold = #export Refute_Core.refute_unfold

  val default_qc_config = Refute_Core.default_qc_config
  val default_mf_config = Refute_Core.default_mf_config
  val default_config = Refute_Core.default_config
  val the_config = Refute_Core.the_config
  val show_config = Refute_Core.show_config
  val upd_timeout = Refute_Core.upd_timeout
  val upd_backends = Refute_Core.upd_backends
  val upd_sequential = Refute_Core.upd_sequential
  val upd_genuine_only = Refute_Core.upd_genuine_only
  val upd_abort_potential = Refute_Core.upd_abort_potential
  val upd_quiet = Refute_Core.upd_quiet
  val upd_no_assms = Refute_Core.upd_no_assms
  val upd_evals = Refute_Core.upd_evals
  val upd_expect = Refute_Core.upd_expect
  val upd_max_counterexamples = Refute_Core.upd_max_counterexamples
  val upd_tag = Refute_Core.upd_tag
  val upd_qc = Refute_Core.upd_qc
  val upd_size = Refute_Core.upd_size
  val upd_iterations = Refute_Core.upd_iterations
  val upd_depth = Refute_Core.upd_depth
  val upd_finite_types = Refute_Core.upd_finite_types
  val upd_finite_type_size = Refute_Core.upd_finite_type_size
  val upd_default_type = Refute_Core.upd_default_type
  val upd_substrate = Refute_Core.upd_substrate
  val upd_allow_function_inversion =
    Refute_Core.upd_allow_function_inversion
  val upd_use_subtype = Refute_Core.upd_use_subtype
  val upd_seed = Refute_Core.upd_seed
  val upd_allow_existentials = Refute_Core.upd_allow_existentials
  val upd_finite_functions = Refute_Core.upd_finite_functions
  val upd_certify = Refute_Core.upd_certify
  val upd_smart_quantifier = Refute_Core.upd_smart_quantifier
  val upd_smart_generators = Refute_Core.upd_smart_generators
  val upd_optimise_equality = Refute_Core.upd_optimise_equality
  val upd_reorder_premises = Refute_Core.upd_reorder_premises
  val upd_mf = Refute_Core.upd_mf
  val upd_card = Refute_Core.upd_card
  val upd_max = Refute_Core.upd_max
  val upd_mono = Refute_Core.upd_mono
  val upd_wf = Refute_Core.upd_wf
  val upd_sat_solver = Refute_Core.upd_sat_solver
  val upd_batch_size = Refute_Core.upd_batch_size
  val upd_falsify = Refute_Core.upd_falsify
  val upd_user_axioms = Refute_Core.upd_user_axioms
  val upd_destroy_constrs = Refute_Core.upd_destroy_constrs
  val upd_total_consts = Refute_Core.upd_total_consts
  val upd_peephole_optim = Refute_Core.upd_peephole_optim
  val upd_datatype_sym_break = Refute_Core.upd_datatype_sym_break
  val upd_kodkod_sym_break = Refute_Core.upd_kodkod_sym_break
  val upd_max_potential = Refute_Core.upd_max_potential
  val upd_max_genuine = Refute_Core.upd_max_genuine
  val upd_atoms = Refute_Core.upd_atoms
  val upd_format = Refute_Core.upd_format
  val upd_show_types = Refute_Core.upd_show_types
  val upd_show_skolems = Refute_Core.upd_show_skolems
  val upd_show_consts = Refute_Core.upd_show_consts
  val upd_debug = Refute_Core.upd_debug
  val upd_overlord = Refute_Core.upd_overlord
  val upd_max_threads = Refute_Core.upd_max_threads
  val upd_tac_timeout = Refute_Core.upd_tac_timeout
  val upd_specialize = Refute_Core.upd_specialize
  val upd_box = Refute_Core.upd_box
  val upd_binary_ints = Refute_Core.upd_binary_ints
  val upd_bits = Refute_Core.upd_bits
  val upd_star_linear_preds = Refute_Core.upd_star_linear_preds
  val upd_iter = Refute_Core.upd_iter
  val upd_bisim_depth = Refute_Core.upd_bisim_depth
  val upd_finitize = Refute_Core.upd_finitize
  val upd_whack = Refute_Core.upd_whack
  val upd_need = Refute_Core.upd_need
  val upd_merge_type_vars = Refute_Core.upd_merge_type_vars
end
