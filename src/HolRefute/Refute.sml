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

  (* Install the native extractor and register the built-in backends through
     this public entry point.  These explicit references also make both
     implementation units dependencies of [load "Refute"]. *)
  val () = Refute_Extract.install_extractor ()
  val () = Refute_QC.register_backends ()
  val () = Refute_ModelFinder.register_backends ()

  val refute = Refute_Core.refute
  fun refute_def tm = refute (!Refute_Core.the_config) tm

  fun refute_goal cfg (assumptions, goal) =
    Refute_Core.refute_problem cfg
      {goal = goal, assumptions = assumptions, evals = []}

  fun refute_top () = refute_goal (!Refute_Core.the_config)
    (proofManagerLib.top_goal ())

  fun quickcheck tm = refute
    (Refute_Core.upd_backends (SOME ["exhaustive", "random"])
      (!Refute_Core.the_config)) tm

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
  val register_codatatype = Refute_ModelFinder_HOL.register_codatatype
  val register_quotient = Refute_ModelFinder_HOL.register_quotient
  val register_typedef = Refute_ModelFinder_HOL.register_typedef
  val register_ersatz = Refute_ModelFinder_HOL.register_ersatz
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
  val upd_smart_quantifier = Refute_Core.upd_smart_quantifier
  val upd_optimise_equality = Refute_Core.upd_optimise_equality
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
end
