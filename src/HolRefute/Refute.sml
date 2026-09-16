structure Refute :> Refute = struct
  (* [open], not one alias per name: the facade re-exports the whole of
     Refute_Core's configuration surface, so a new option costs an edit
     in Refute_Core and one in Refute.sig, and none here. *)
  open Refute_Core

  type goal = term list * term
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

  (* Deliberately shadows [Refute_Core.config_update], the internal
     update descriptor: the user-facing update is a function. *)
  type config_update = config -> config

  (* Register the built-in backends through this public entry point.
     Refute_QC passes the native extractor explicitly, making both
     implementation units dependencies of [load "Refute"]. *)
  val () = Refute_QC.register_backends ()
  val () = Refute_QC_Narrow.register_backend ()
  val () = Refute_ModelFinder.register_backends ()
  (* Rational and real Frac encoding and display are part of the default
     session setup; the normalization-faithfulness corpus in selftest.sml
     keeps them honest. *)
  val () = Refute_ModelFinder_Model.register_frac_type_rat ()
  val () = Refute_ModelFinder_Model.register_frac_type_real ()
  (* fmap's model-finder typedef (Refute_ModelFinder_HOL.sml) is itself
     unconditional, so its display is installed unconditionally too. *)
  val () = Refute_ModelFinder_Model.register_fmap_display ()
  (* Update-chain dedup applies to every function type, so it too is
     unconditional; see the comment on [dedup_update_chain]. *)
  val () = Refute_ModelFinder_Model.register_function_display ()
  (* Quickcheck generator and compset fragment for :rat and :real,
     independent of the model-finder Frac registration above. *)
  val () = Refute_EvalRat.register ()
  val () = Refute_EvalReal.register ()
  (* Equality decision for ground finite maps: without it computeLib only
     decides [fm = fm'] for identical chains, and the Compute substrate
     can never confirm a candidate whose conclusion is such an equality. *)
  val () = Refute_EvalFmap.register ()
  (* Finite maps: FEMPTY/FUPDATE fit the same constructor-registration
     shape as an abstract type, generalized to fire for every concrete
     instance of the fmap type operator.  Unlike :rat/:real, this yields an
     ordinary GenDatatype (exhaustive = false, since the key type is
     generally infinite); only Compute can produce fmap candidates today
     (NativeSML rejects every registered generator, see Refute_Extract's
     [validate_type]).
     FEMPTY |+ (1,2) |+ (1,3) and FEMPTY |+ (1,3) denote the same map, so
     an FUPDATE chain has no unique syntactic form.  [canonical_fmap_chain]
     removes an update iff a later update in the same chain has an [aconv]
     key, keeping every survivor at its original position.  This is
     denotation-preserving for any key type: a later [aconv] match shadows
     the earlier write completely, regardless of what the keys denote.  It
     is deliberately not a sort: sorting needs the keys known pairwise
     distinct as values, which [Term.compare] cannot decide, so two chains
     denoting the same map are not guaranteed to display identically. *)
  fun canonical_fmap_chain term =
    let
      val (base, pairs) = finite_mapSyntax.strip_fupdate term
    in
      if not (finite_mapSyntax.is_fempty base) then term
      else
        let
          val keyed = List.map pairSyntax.dest_pair pairs
          fun keep ((key, value), (kept, seen)) =
            if Refute_Util.aconv_member key seen
            then (kept, key :: seen)
            else ((key, value) :: kept, key :: seen)
          val (kept, _) = List.foldr keep ([], []) keyed
        in
          finite_mapSyntax.list_mk_fupdate
            (base, List.map pairSyntax.mk_pair kept)
        end
    end
  val () = Refute_Gen.register_generator_family
    {tyop = {Thy = "finite_map", Tyop = "fmap"},
     constructors = [finite_mapSyntax.fempty_tm, finite_mapSyntax.fupdate_tm],
     canonical = SOME canonical_fmap_chain}
  (* [Refute_Gen] cannot register this directly with the model finder --
     it has no dependency on [Refute_ModelFinder_Model] -- so this module,
     which depends on both, installs the callback.  This is the single
     source [Refute_QC.record_candidate_with] now consults through the
     shared walk, replacing its own former copy of the same lookup. *)
  val () = Refute_ModelFinder_Model.register_family_canonical_lookup
    Refute_Gen.snapshot_family_canonicals

  fun refute_def tm = refute (!the_config) tm

  fun apply_updates updates config =
    List.foldl (fn (update, current) => update current) config updates

  fun current_config updates =
    apply_updates updates (!the_config)

  fun backend_name Exhaustive = "exhaustive"
    | backend_name Random = "random"
    | backend_name Narrowing = "narrowing"
    | backend_name ModelFinder = "kodkod"
    | backend_name (RegisteredBackend name) = name

  fun upd_search AllBackends = upd_backends NONE
    | upd_search QuickcheckBackends = upd_backends
        (SOME (Refute_QC.qc_backend_names ()))
    | upd_search (Only []) =
        raise Feedback.mk_HOL_ERR "Refute" "upd_search"
          "Only requires at least one backend"
    | upd_search (Only choices) =
        upd_backends (SOME (map backend_name choices))

  fun refute_with updates tm = refute (current_config updates) tm

  fun refute_goal cfg (assumptions, goal) =
    refute_problem cfg
      {goal = goal, assumptions = assumptions, evals = []}

  fun refute_goal_with updates goal =
    refute_goal (current_config updates) goal

  fun refute_top () = refute_goal (!the_config)
    (proofManagerLib.top_goal ())

  val try_seed = 42

  fun try_refute cfg (assumptions, goal) =
    let
      val try_config = cfg
        |> upd_sequential true
        |> upd_seed (SOME try_seed)
        |> upd_expect NoExpectation
        |> upd_quiet true
    in
      case refute_problem try_config
             {goal = goal, assumptions = assumptions, evals = []} of
          outcome as Counterexample (cex :: _) =>
            SOME (#backend cex, outcome)
        | _ => NONE
    end
    handle Time.Time => NONE

  fun qc_only config = upd_search QuickcheckBackends config

  (* The option distinguishes the QC-only convenience from an explicitly
     supplied configuration whose [backends = NONE] means the full registry. *)
  fun unused_config NONE = qc_only (!the_config)
    | unused_config (SOME config) = config

  fun check_unused_assms config named_theorem =
    Refute_Unused.check_unused_assms (unused_config config) named_theorem

  fun find_unused_assms config theory =
    Refute_Unused.find_unused_assms (unused_config config) theory

  fun print_unused_assms config theory =
    Refute_Unused.print_unused_assms (unused_config config) theory

  fun quickcheck tm = refute_with [upd_search QuickcheckBackends] tm

  fun model_refute tm = refute_with [upd_search (Only [ModelFinder])] tm

  fun REFUTE_CONFIG_TAC config goal =
    (refute_goal config goal; Tactical.ALL_TAC goal)

  fun REFUTE_TAC_WITH updates goal =
    REFUTE_CONFIG_TAC (current_config updates) goal

  fun REFUTE_TAC goal =
    REFUTE_TAC_WITH [] goal

  fun QUICKCHECK_TAC goal =
    REFUTE_TAC_WITH [upd_search QuickcheckBackends] goal

  fun NARROWING_TAC goal =
    REFUTE_TAC_WITH [upd_search (Only [Narrowing])] goal

  fun MODEL_REFUTE_TAC goal =
    REFUTE_TAC_WITH [upd_search (Only [ModelFinder])] goal

  val register_generator = Refute_Gen.register_generator
  val register_generator_family = Refute_Gen.register_generator_family
  val register_term_postprocessor =
    Refute_ModelFinder_Model.register_term_postprocessor
  fun register_codatatype registration =
    Refute_ModelFinder_HOL.with_registration_lock (fn () =>
      Refute_ModelFinder_HOL.register_codatatype registration)
  val register_quotient = Refute_ModelFinder_HOL.register_quotient
  val register_typedef = Refute_ModelFinder_HOL.register_typedef
  val harvest_registrations = Refute_ModelFinder_HOL.harvest_registrations
  val register_frac_type = Refute_ModelFinder_HOL.register_frac_type
  fun register_ersatz registration =
    Refute_ModelFinder_HOL.with_registration_lock (fn () =>
      Refute_ModelFinder_HOL.register_ersatz registration)
  val abstract_generator = Refute_Gen.abstract_generator

  val export_refute_simp = #export refute_simp
  val export_refute_psimp = #export refute_psimp
  val export_refute_unfold = #export refute_unfold
end
