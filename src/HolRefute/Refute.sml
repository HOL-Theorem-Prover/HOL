structure Refute :> Refute = struct
  type term = Term.term
  type thm = Thm.thm
  type hol_type = Type.hol_type
  type goal = term list * term

  datatype certainty = datatype Refute_Core.certainty
  type counterexample = Refute_Core.counterexample
  datatype outcome = datatype Refute_Core.outcome
  datatype expectation = datatype Refute_Core.expectation
  datatype substrate_choice = datatype Refute_Core.substrate_choice
  type qc_config = Refute_Core.qc_config
  type config = Refute_Core.config
  type backend = Refute_Core.backend
  type custom_gen = Refute_Gen.custom_gen
  type rng = Refute_Gen.rng

  (* Registering the built-in exhaustive/random backends is a load-time
     side effect in Refute_QC.  Call it here so the backends are available
     through this public entry point; without this reference Refute_QC is
     never loaded and no backend is registered. *)
  val () = Refute_QC.register_backends ()

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

  fun REFUTE_TAC goal =
    case refute_goal (!Refute_Core.the_config) goal of
        Refute_Core.Counterexample cexs =>
          raise Feedback.mk_HOL_ERR "Refute" "REFUTE_TAC"
            (Refute_Core.format_outcome (!Refute_Core.the_config)
              (Refute_Core.Counterexample cexs))
      | _ => Tactical.ALL_TAC goal

  val register_backend = Refute_Core.register_backend
  val register_generator = Refute_Gen.register_generator
  val abstract_generator = Refute_Gen.abstract_generator

  val export_refute_simp = #export Refute_Core.refute_simp
  val export_refute_psimp = #export Refute_Core.refute_psimp
  val export_refute_unfold = #export Refute_Core.refute_unfold

  val default_qc_config = Refute_Core.default_qc_config
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
end
