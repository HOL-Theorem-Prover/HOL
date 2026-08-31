structure Refute_Cert_Model = struct
  open Refute_Cert
  structure Util = Refute_Util
  structure MFH = Refute_ModelFinder_HOL
  structure Skolem = Refute_Skolem

  datatype result =
      Certified of Thm.thm
    | NoCertificate of string
    | DiscardedByWholeFormulaEval

  datatype replay_attempt_kind =
      Exact
    | Schematic
    | ChosenCompletion

  datatype failure_kind =
      NoProof
    | Unsupported
    | MalformedInput
    | TrustRejected
    | FuelExhausted
    | DeadlineExhausted
    | InternalFailure

  type failure =
    {kind : failure_kind,
     stage : string,
     depth : int,
     detail : string}

  datatype candidate_source =
      OrdinaryBinding
    | ReconstructedSkolem
    | ReconstructedTypeValue
    | GenericHint
    | ActiveVariable
    | FunctionApplication
    | SynthesizedConstructor

  type dependency = Skolem.dependency
  type provenance = Skolem.info
  datatype replay_hint_source =
      SkolemValue
    | TypeValue
    | DirectHint
  type replay_hint =
    {term : term,
     source : replay_hint_source,
     provenance : provenance option}

  type candidate =
    {term : term,
     source : candidate_source,
     provenance : provenance option}

  type policy =
    {total_fuel : int,
     max_generated_candidates : int,
     max_attempted_candidates : int,
     max_completion_candidates : int,
     max_completion_vectors : int,
     max_function_states : int,
     max_constructor_depth : int,
     max_constructor_width : int,
     max_constructor_size : int,
     max_split_depth : int,
     max_case_branches : int,
     max_inductions : int,
     max_leaf_rounds : int,
     enable_whole_formula : bool,
     enable_cases : bool,
     enable_induction : bool,
     enable_synthesis : bool,
     enable_taut : bool,
     enable_omega : bool,
     enable_real_arith : bool}

  type diagnostics =
    {nodes : int,
     ordinary_bindings : int,
     reconstructed_hints : int,
     active_candidates : int,
     applications : int,
     constructor_terms : int,
     generated_candidates : int,
     function_states : int,
     attempted_candidates : int,
     memo_hits : int,
     case_branches : int,
     induction_attempts : int,
     leaf_attempts : int,
     real_arith_attempts : int,
     schematic_attempts : int,
     completion_attempts : int,
     candidate_trace : (int * term * term) list,
     consumed_fuel : int,
     elapsed : Time.time,
     failure : failure option}

  exception ReplayFailure of failure
  exception CandidateSuccess of Thm.thm

  val replay_candidate_limit = 128

  fun default_policy fuel : policy =
    {total_fuel = Int.max (0, fuel),
     max_generated_candidates = replay_candidate_limit,
     max_attempted_candidates = replay_candidate_limit,
     max_completion_candidates = 16,
     max_completion_vectors = replay_candidate_limit,
     max_function_states = 256,
     max_constructor_depth = 2,
     max_constructor_width = 32,
     max_constructor_size = 12,
     max_split_depth = 1,
     max_case_branches = 32,
     max_inductions = 2,
     max_leaf_rounds = 2,
     enable_whole_formula = true,
     enable_cases = true,
     enable_induction = true,
     enable_synthesis = true,
     enable_taut = true,
     enable_omega = true,
     enable_real_arith = true}

  fun policy_for_test
        {fuel, cases, induction, synthesis, taut, omega, real_arith,
         split_depth, branches, constructor_depth, constructor_width} :
        policy =
    {total_fuel = Int.max (0, fuel),
     max_generated_candidates = replay_candidate_limit,
     max_attempted_candidates = replay_candidate_limit,
     max_completion_candidates = 16,
     max_completion_vectors = replay_candidate_limit,
     max_function_states = 256,
     max_constructor_depth = Int.max (0, constructor_depth),
     max_constructor_width = Int.max (0, constructor_width),
     max_constructor_size = 12,
     max_split_depth = Int.max (0, split_depth),
     max_case_branches = Int.max (0, branches),
     max_inductions = 2,
     max_leaf_rounds = 2,
     enable_whole_formula = false,
     enable_cases = cases,
     enable_induction = induction,
     enable_synthesis = synthesis,
     enable_taut = taut,
     enable_omega = omega,
     enable_real_arith = real_arith}

  fun portfolio_policy_for_test {fuel, candidates, vectors} : policy =
    {total_fuel = Int.max (0, fuel),
     max_generated_candidates = replay_candidate_limit,
     max_attempted_candidates = replay_candidate_limit,
     max_completion_candidates = Int.max (0, candidates),
     max_completion_vectors = Int.max (0, vectors),
     max_function_states = 256,
     max_constructor_depth = 2,
     max_constructor_width = 32,
     max_constructor_size = 12,
     max_split_depth = 1,
     max_case_branches = 32,
     max_inductions = 2,
     max_leaf_rounds = 2,
     enable_whole_formula = true,
     enable_cases = true,
     enable_induction = true,
     enable_synthesis = false,
     enable_taut = true,
     enable_omega = true,
     enable_real_arith = true}

  fun failure_kind_name NoProof = "no-proof"
    | failure_kind_name Unsupported = "unsupported"
    | failure_kind_name MalformedInput = "malformed-input"
    | failure_kind_name TrustRejected = "trust-rejected"
    | failure_kind_name FuelExhausted = "fuel-exhausted"
    | failure_kind_name DeadlineExhausted = "deadline-exhausted"
    | failure_kind_name InternalFailure = "internal-failure"

  fun render_failure ({kind, stage, depth, detail} : failure) =
    "model replay [" ^ failure_kind_name kind ^ "] " ^ stage ^
    " at depth " ^ Int.toString depth ^ ": " ^ detail

  (* [realLib.REAL_ARITH] is a prover ([term -> thm]), not a [conv]; the
     other two leaf decision procedures are already [conv]s, so wrap it
     the same way as [Drule.EQT_INTRO]. *)
  fun real_arith_conv goal = Drule.EQT_INTRO (realLib.REAL_ARITH goal)

  (* [REAL_ARITH] is two provers (the second Positivstellensatz-based)
     behind one flat fuel charge, so [decision_leaf] must not spend it
     on goals with no [:real] subterm at all - unlike
     [TAUT_CONV]/[OMEGA_CONV], it cannot even apply. *)
  fun mentions_real goal =
    Lib.can (HolKernel.find_term
      (fn tm => Util.same_type (Term.type_of tm) realSyntax.real_ty)) goal

  fun theorem_acceptable expected theorem =
    null (Thm.hyp theorem) andalso trusted theorem andalso
    (case expected of
         NONE => true
       | SOME conclusion => Term.aconv (Thm.concl theorem) conclusion)

  val audit_theorem_for_test = theorem_acceptable

  fun app_combinations_bounded limit emit choices =
    let
      val emitted = ref 0

      fun combinations [] prefix =
            if !emitted >= limit then ()
            else
              (emitted := !emitted + 1;
               emit (rev prefix))
        | combinations (options :: rest) prefix =
            let
              fun traverse [] = ()
                | traverse (option :: remaining) =
                    if !emitted >= limit then ()
                    else
                      (combinations rest (option :: prefix);
                       traverse remaining)
            in
              traverse options
            end
    in
      if limit <= 0 then () else combinations choices [];
      !emitted
    end

  fun combination_count_for_test limit choices =
    app_combinations_bounded limit (fn _ => ()) choices

  fun candidate_size tm =
    let
      fun size candidate =
        let val (_, arguments) = boolSyntax.strip_comb candidate
        in
          1 + List.foldl (fn (argument, total) =>
            size argument + total) 0 arguments
        end
    in
      size tm
    end

  (* The replay witness pool and the completion portfolio deliberately share
     one bounded, type-directed constructor generator. *)
  fun synth_values_bounded
        {target, pool, active, max_depth, width, max_size,
         resolve, charge} =
    let
      val initial = List.filter (fn candidate =>
        Util.same_type target (Term.type_of candidate)) (pool @ active)
      val values = ref (rev initial)
      val count = ref (length (!values))

      fun add value =
        if !count >= width orelse candidate_size value > max_size orelse
           Util.aconv_member value (!values)
        then ()
        else (values := value :: !values; count := !count + 1)

      fun build depth =
        case resolve target of
            NONE => ()
          | SOME constructors =>
              let
                fun one constructor =
                  let
                    val argument_types =
                      MFH.constructor_arg_types constructor
                    val choices =
                      if depth <= 0 andalso not (null argument_types) then []
                      else map (fn ty => synth_values_bounded
                        {target = ty, pool = pool, active = active,
                         max_depth = depth - 1, width = width,
                         max_size = max_size, resolve = resolve,
                         charge = charge}) argument_types
                    fun emit arguments =
                      let val term = Term.list_mk_comb
                        (constructor, arguments)
                      in charge (); add term end
                  in
                    if null argument_types then add constructor
                    else if depth <= 0 orelse List.exists null choices then ()
                    else ignore (app_combinations_bounded width emit choices)
                  end
              in
                List.app one constructors
              end
    in
      build max_depth;
      rev (!values)
    end

  fun certify_detailed_rich {original, env, hints, policy, deadline} =
    let
      val hint_terms = map #term (hints : replay_hint list)
      val start = Time.now ()
      val remaining = ref (#total_fuel policy)
      val nodes = ref 0
      val ordinary_bindings = ref 0
      val reconstructed_hints = ref 0
      val active_candidates = ref 0
      val applications = ref 0
      val constructor_terms = ref 0
      val attempted_candidates = ref 0
      val memo_hits = ref 0
      val case_branches = ref 0
      val induction_attempts = ref 0
      val leaf_attempts = ref 0
      val real_arith_attempts = ref 0
      val generated_candidates = ref 0
      val function_states = ref 0
      val candidate_trace = ref ([] : (int * term * term) list)

      fun failure kind stage depth detail =
        ReplayFailure
          {kind = kind, stage = stage, depth = depth, detail = detail}

      fun fail kind stage depth detail =
        raise failure kind stage depth detail

      fun check_deadline stage depth =
        case deadline of
            SOME limit =>
              if Time.now () >= limit then
                fail DeadlineExhausted stage depth
                  "replay deadline exhausted"
              else ()
          | NONE => ()

      fun charge stage depth =
        let
          val _ = check_deadline stage depth
        in
          if !remaining <= 0 then
            fail FuelExhausted stage depth "replay fuel exhausted"
          else
            remaining := !remaining - 1
        end

      fun within_deadline stage depth operation input =
        let
          val _ = check_deadline stage depth
          val result =
            case deadline of
                NONE => operation input
              | SOME limit =>
                  let val allowance = Time.- (limit, Time.now ())
                  in
                    if Time.<= (allowance, Time.zeroTime) then
                      fail DeadlineExhausted stage depth
                        "replay deadline exhausted"
                    else
                      Timeout.apply allowance operation input
                  end
                  handle Timeout.TIMEOUT _ =>
                    fail DeadlineExhausted stage depth
                      "proof operation timed out"
          val _ = check_deadline stage depth
        in
          result
        end

      fun require_theorem stage depth expected theorem =
        let val _ = check_deadline stage depth
        in
          if theorem_acceptable expected theorem then theorem
          else fail TrustRejected stage depth
            "theorem has hypotheses, an unacceptable tag, or a wrong endpoint"
        end

      fun resource_failure ({kind, ...} : failure) =
        kind = DeadlineExhausted orelse kind = FuelExhausted

      (* A speculative proof step reports its own failure as NONE, but a
         spent budget belongs to the whole replay and keeps propagating. *)
      fun optional attempt =
        attempt ()
        handle Interrupt => raise Interrupt
             | ReplayFailure issue =>
                 if resource_failure issue then raise ReplayFailure issue
                 else NONE
             | _ => NONE

      fun optional_equality stage depth input operation =
        optional (fn () =>
          let
            val _ = charge stage depth
            val theorem = within_deadline stage depth operation input
          in
            if theorem_acceptable
                 (SOME (boolSyntax.mk_eq (input, rhs_of theorem))) theorem
            then SOME theorem
            else NONE
          end)

      fun portfolio depth tm =
        equality_portfolio (#max_leaf_rounds policy)
          (fn stage => optional_equality stage depth) tm

      fun prove_by_conversion stage depth conversion goal =
        optional (fn () =>
          let
            val _ = charge stage depth
            val equality = within_deadline stage depth conversion goal
            val equality = require_theorem stage depth
              (SOME (boolSyntax.mk_eq (goal, boolSyntax.T))) equality
            val theorem = Drule.EQT_ELIM equality
          in
            SOME (require_theorem stage depth (SOME goal) theorem)
          end)

      fun direct_leaf depth formula =
        let
          val _ = leaf_attempts := !leaf_attempts + 1
        in
          case portfolio depth formula of
              SOME theorem =>
                if Term.aconv (rhs_of theorem) boolSyntax.F then
                  SOME (require_theorem "leaf equality elimination" depth
                    (SOME (boolSyntax.mk_neg formula))
                    (Drule.EQF_ELIM theorem))
                else NONE
            | NONE => NONE
        end

      (* First success wins; each entry is skipped when its decision
         procedure is disabled or inapplicable. *)
      fun decision_leaf depth formula =
        let
          val goal = boolSyntax.mk_neg formula
          fun attempt (enabled, name, conv) =
            if enabled then prove_by_conversion name depth conv goal
            else NONE
        in
          Lib.get_first attempt
            [(#enable_taut policy, "propositional leaf", tautLib.TAUT_CONV),
             (#enable_omega policy, "Presburger leaf", Omega.OMEGA_CONV),
             (#enable_real_arith policy andalso mentions_real goal,
              "real linear arithmetic leaf", real_arith_conv)]
        end

      val (variables, closure, body) = closure_of original
      val expected = boolSyntax.mk_neg closure
      val instance = instantiate env body

      fun fast_certificate theorem =
        let
          val negated_instance = Drule.EQF_ELIM theorem
          val witnesses = map (instantiate env) variables
          val certificate = refute_forall closure witnesses negated_instance
          val certificate = conform_conclusion
            "whole-formula replay" expected certificate
        in
          require_theorem "whole-formula replay" 0
            (SOME expected) certificate
        end

      fun whole_formula () =
        case evaluate_instance (#max_leaf_rounds policy)
          (fn stage => optional_equality stage 0) instance of
            InstanceFalse theorem =>
              SOME (Certified (fast_certificate theorem))
          | InstanceTrue =>
              if null (Term.free_vars_lr instance) then
                SOME DiscardedByWholeFormulaEval
              else NONE
          | InstanceStuck _ => NONE

      fun replay_pnf () =
        let
          val normalization_stage = ref "normalization"
          fun normalization_step conversion tm =
            let
              val stage = !normalization_stage
              val _ = charge stage 0
              val theorem = within_deadline stage 0
                (fn input => conversion input
                  handle Conv.UNCHANGED => Thm.REFL input) tm
              val theorem = require_theorem stage 0
                (SOME (boolSyntax.mk_eq (tm, rhs_of theorem))) theorem
              val _ = normalization_stage := "prenex conversion"
            in
              theorem
            end
          val (normalized_equality, prenex_equality, pnf) =
            normalize_to_pnf normalization_step closure

          fun quantified tm =
            boolSyntax.is_forall tm orelse boolSyntax.is_exists tm
          fun quantifier_free tm =
            not (Lib.can (HolKernel.find_term quantified) tm)
          val matrix = #2 (Refute_Narrow.strip_quantifiers pnf)
          val _ =
            if quantifier_free matrix then ()
            else fail MalformedInput "prenex conversion" 0
              "a quantifier remains outside the prenex prefix"

          val binding_pool = Util.distinct_terms (map #2 env)
          fun add_hint_unique
                (hint as {term, ...} : replay_hint, accumulated) =
            if List.exists (fn ({term = old, ...} : replay_hint) =>
                 Term.aconv old term) accumulated then accumulated
            else hint :: accumulated
          val hint_pool = rev (List.foldl add_hint_unique [] hints)
          val hint_pool_terms = map #term hint_pool
          val pool_base = binding_pool @ hint_pool_terms
          val base_avoids = Util.distinct_terms (List.concat
            (map Term.all_vars
              (original :: map #1 env @ map #2 env @ hint_terms)))

          type split_row = term * int
          type origin_row = term * int option
          type replay_context =
            {active : term list,
             active_origins : origin_row list,
             next_origin : int,
             split_depths : split_row list}

          type failed_state =
            {formula : term,
             active_types : Type.hol_type list,
             split_depths : int list,
             cases_allowed : bool,
             induction_allowed : bool}

          (* Keyed on the abstracted formula alone: Term.compare is the
             alpha-equivalence order that same_state's own aconv test uses,
             so states that same_state identifies always share a bucket. *)
          val failed = ref
            (Redblackmap.mkDict Term.compare :
              (term, failed_state list) Redblackmap.dict)

          fun abstract active tm = Term.list_mk_abs (active, tm)
          fun same_types (left, right) =
            length left = length right andalso
            ListPair.allEq (fn (a, b) => Util.same_type a b)
              (left, right)
          fun depth_of rows variable =
            Option.getOpt (Lib.op_assoc1 Term.aconv variable rows, 0)
          fun state formula
                ({active, split_depths, ...} : replay_context)
                : failed_state =
            {formula = abstract active formula,
             active_types = map Term.type_of active,
             split_depths = map (depth_of split_depths) active,
             cases_allowed = #enable_cases policy,
             induction_allowed = #enable_induction policy}
          fun same_state (left : failed_state) (right : failed_state) =
            Term.aconv (#formula left) (#formula right) andalso
            same_types (#active_types left, #active_types right) andalso
            #split_depths left = #split_depths right andalso
            #cases_allowed left = #cases_allowed right andalso
            #induction_allowed left = #induction_allowed right
          fun bucket current =
            Option.getOpt
              (Redblackmap.peek (!failed, #formula current), [])
          fun seen current =
            List.exists (fn old => same_state old current) (bucket current)
          fun remember current =
            let val existing = bucket current
            in
              if List.exists (fn old => same_state old current) existing then
                ()
              else failed := Redblackmap.insert
                (!failed, #formula current, current :: existing)
            end

          fun no_proof stage depth detail =
            fail NoProof stage depth detail

          fun is_no_proof ({kind, ...} : failure) = kind = NoProof

          (* is_codatatype walks the theory ancestry, so the model-specific
             filter remains in this cache in front of the shared TypeBase
             constructor resolver. *)
          val resolve_typebase = constructor_resolver ()
          val constructor_cache = ref
            (Redblackmap.mkDict Type.compare :
              (Type.hol_type,
               (TypeBasePure.tyinfo * term list) option) Redblackmap.dict)

          fun resolve_constructors ty =
            if MFH.is_codatatype ty then NONE
            else
              case resolve_typebase ty of
                  NONE => NONE
                | SOME constructors =>
                    if null constructors then NONE
                    else Option.map (fn info => (info, constructors))
                      (TypeBase.fetch ty)
            handle Feedback.HOL_ERR _ => NONE

          fun constructor_info ty =
            case Redblackmap.peek (!constructor_cache, ty) of
                SOME resolved => resolved
              | NONE =>
                  let val resolved = resolve_constructors ty
                  in
                    constructor_cache :=
                      Redblackmap.insert (!constructor_cache, ty, resolved);
                    resolved
                  end

          fun bump_source OrdinaryBinding =
                ordinary_bindings := !ordinary_bindings + 1
            | bump_source ReconstructedSkolem =
                reconstructed_hints := !reconstructed_hints + 1
            | bump_source ReconstructedTypeValue =
                reconstructed_hints := !reconstructed_hints + 1
            | bump_source GenericHint =
                reconstructed_hints := !reconstructed_hints + 1
            | bump_source ActiveVariable =
                active_candidates := !active_candidates + 1
            | bump_source FunctionApplication =
                applications := !applications + 1
            | bump_source SynthesizedConstructor =
                constructor_terms := !constructor_terms + 1

          fun emit_candidate seen_terms attempt
                (entry as {term, source, ...} : candidate) =
            if HOLset.member (!seen_terms, term) then ()
            else if !generated_candidates >=
                    #max_generated_candidates policy then
              ()
            else
              let
                val _ = generated_candidates := !generated_candidates + 1
                val _ = bump_source source
                val _ = seen_terms := HOLset.add (!seen_terms, term)
              in
                attempt entry
              end

          fun generate_candidates depth target target_origin active
                active_origins attempt =
            let
              val seen_terms = ref (HOLset.empty Term.compare)
              fun emit entry = emit_candidate seen_terms attempt entry
              fun emit_terms source terms = List.app (fn term => emit
                {term = term, source = source, provenance = NONE}) terms

              val direct_bindings = List.filter (fn term =>
                Util.same_type target (Term.type_of term)) binding_pool
              fun matching_hints source = List.filter
                (fn ({term, source = actual, ...} : replay_hint) =>
                  source = actual andalso
                  Util.same_type target (Term.type_of term)) hint_pool
              val direct_skolems = matching_hints SkolemValue
              val direct_types = matching_hints TypeValue
              val direct_generic = matching_hints DirectHint
              val direct_active = List.filter (fn term =>
                Util.same_type target (Term.type_of term)) active

              fun emit_hint candidate_source
                    ({term, provenance, ...} : replay_hint) =
                emit {term = term, source = candidate_source,
                  provenance = provenance}

              fun application_walk current [] = ()
                | application_walk current (variable :: rest) =
                    if !function_states >= #max_function_states policy then ()
                    else
                      (case Lib.total Type.dom_rng
                          (Term.type_of current) of
                           NONE => ()
                         | SOME (domain, _) =>
                             if Util.same_type domain
                                  (Term.type_of variable) then
                               let
                                 val _ = function_states :=
                                   !function_states + 1
                                 val _ = charge
                                   "candidate application generation" depth
                                 val applied =
                                   Term.mk_comb (current, variable)
                                 val _ =
                                   if Util.same_type target
                                        (Term.type_of applied) then
                                     emit
                                       {term = applied,
                                        source = FunctionApplication,
                                        provenance = NONE}
                                   else ()
                               in
                                 application_walk applied rest;
                                 application_walk current rest
                               end
                             else application_walk current rest)

              fun applications_of base = application_walk base active

              fun exact_dependency_arguments dependencies =
                let
                  fun find ({origin, source_type} : dependency) =
                    case List.find (fn (variable, candidate_origin) =>
                      candidate_origin = SOME origin andalso
                      Util.same_type source_type
                        (Term.type_of variable)) active_origins of
                        SOME (variable, _) => SOME variable
                      | NONE => NONE
                  fun collect [] result = SOME (rev result)
                    | collect (dependency :: rest) result =
                        (case find dependency of
                             SOME variable =>
                               collect rest (variable :: result)
                           | NONE => NONE)
                in
                  collect dependencies []
                end

              fun provenance_application
                    ({term, provenance = SOME metadata, ...} : replay_hint) =
                    if #origin metadata <> SOME target_origin then ()
                    else
                    (case exact_dependency_arguments
                        (#dependencies metadata) of
                         NONE => ()
                       | SOME arguments =>
                           (case Lib.total Term.list_mk_comb
                               (term, arguments) of
                                SOME applied =>
                                  if Util.same_type target
                                       (Term.type_of applied) then
                                    emit
                                      {term = applied,
                                       source = FunctionApplication,
                                       provenance = SOME metadata}
                                  else ()
                              | NONE => ()))
                | provenance_application _ = ()

              fun synthesized () =
                if not (#enable_synthesis policy) then ()
                else
                  let
                    val known = pool_base @ active
                    val generated = synth_values_bounded
                      {target = target, pool = pool_base, active = active,
                       max_depth = #max_constructor_depth policy,
                       width = #max_constructor_width policy,
                       max_size = #max_constructor_size policy,
                       resolve = fn ty => Option.map #2
                         (constructor_info ty),
                       charge = fn () => charge
                         "constructor synthesis" 0}
                    val new = List.filter (fn term =>
                      not (Util.aconv_member term known)) generated
                  in
                    emit_terms SynthesizedConstructor new
                  end
            in
              List.app (emit_hint ReconstructedSkolem)
                (List.filter (fn
                  ({provenance = SOME metadata, ...} : replay_hint) =>
                    #origin metadata = SOME target_origin
                  | _ => false) direct_skolems);
              emit_terms OrdinaryBinding direct_bindings;
              List.app (emit_hint ReconstructedSkolem) direct_skolems;
              (* [DirectHint] (an explicitly-supplied targeted hint, e.g.
                 the real-Frac literal) before [TypeValue] (bulk type
                 enumeration): a targeted hint must not be starved by
                 [max_generated_candidates] behind same-typed filler. *)
              List.app (emit_hint GenericHint) direct_generic;
              List.app (emit_hint ReconstructedTypeValue) direct_types;
              emit_terms ActiveVariable direct_active;
              List.app provenance_application hint_pool;
              List.app applications_of pool_base;
              synthesized ()
            end

          fun contains_type target ty =
            Util.same_type target ty orelse
            (case Lib.total Type.dest_type ty of
                 SOME (_, arguments) =>
                   List.exists (contains_type target) arguments
               | NONE => false)

          fun regular_recursive_type ty constructors =
            let
              val all_arguments =
                List.concat (map MFH.constructor_arg_types constructors)
              val direct = List.exists (Util.same_type ty) all_arguments
              val nested = List.exists (fn argument =>
                not (Util.same_type ty argument) andalso
                contains_type ty argument) all_arguments
            in
              direct andalso not nested
            end

          fun single_property_induction ty theorem =
            let
              val (_, conclusion) = boolSyntax.strip_forall
                (Thm.concl theorem)
              val (_, consequent) = boolSyntax.dest_imp conclusion
              val (objects, property) = boolSyntax.strip_forall consequent
              val (head, arguments) = boolSyntax.strip_comb property
              val object_ty = Term.type_of (hd objects)
              val type_matches = Option.isSome
                (Lib.total (fn actual => Type.match_type actual ty)
                  object_ty)
            in
              length objects = 1 andalso length arguments = 1 andalso
              type_matches andalso
              Term.aconv (hd arguments) (hd objects) andalso
              Term.is_var head
            end
            handle Feedback.HOL_ERR _ => false

          fun local_induction_tactic depth : Abbrev.tactic =
            let
              val introductions = Tactical.REPEAT
                (Tactical.FIRST
                  [Tactic.CONJ_TAC, Tactic.GEN_TAC])
              val assumptions = Tactical.REPEAT Tactic.DISCH_TAC
              val simplify_goal =
                simpLib.ASM_SIMP_TAC (BasicProvers.srw_ss ()) []
              val taut_goal =
                if #enable_taut policy then
                  Tactical.TRY tautLib.ASM_TAUT_TAC
                else Tactical.ALL_TAC
              val omega_goal =
                if #enable_omega policy then
                  Tactical.TRY Omega.OMEGA_TAC
                else Tactical.ALL_TAC
              (* Unlike [decision_leaf]'s single-formula gate,
                 [REAL_ASM_ARITH_TAC] consumes assumptions too, so the
                 gate must see the whole goal - every assumption plus the
                 conclusion - not the conclusion alone. *)
              fun real_goal (goal as (asl, w)) =
                if #enable_real_arith policy andalso
                   List.exists mentions_real (w :: asl)
                then
                  (real_arith_attempts := !real_arith_attempts + 1;
                   Tactical.TRY realLib.REAL_ASM_ARITH_TAC goal)
                else Tactical.ALL_TAC goal
              fun account goal =
                (charge "induction constructor obligation" depth;
                 leaf_attempts := !leaf_attempts + 1;
                 Tactical.EVERY
                   [introductions, simplify_goal, assumptions,
                    simplify_goal, taut_goal, omega_goal, real_goal]
                   goal)
            in
              account
            end

          fun prove_neg formula context depth =
            let
              val _ = charge "replay node" depth
              val _ = nodes := !nodes + 1
              val current = state formula context
              val _ = if seen current then
                  (memo_hits := !memo_hits + 1;
                   no_proof "memoization" depth
                     "state already failed with these strategy permissions")
                else ()

              fun ordinary () =
                if boolSyntax.is_forall formula then
                  let
                    val (variable, body) = boolSyntax.dest_forall formula
                    val target = Term.type_of variable

                    fun attempt
                          ({term = witness, ...} : candidate) =
                      if !attempted_candidates >=
                           #max_attempted_candidates policy then ()
                      else
                        let
                          val _ = attempted_candidates :=
                            !attempted_candidates + 1
                          val _ = charge "candidate branch" depth
                          val instance = Term.subst
                            [{redex = variable, residue = witness}] body
                          val _ = candidate_trace :=
                            (depth, witness, instance) :: !candidate_trace
                          val next : replay_context =
                            {active = #active context,
                             active_origins = #active_origins context,
                             next_origin = #next_origin context + 1,
                             split_depths = #split_depths context}
                          val refutation =
                            prove_neg instance next (depth + 1)
                          val theorem =
                            refute_forall formula [witness] refutation
                          val theorem = require_theorem
                            "universal replay" depth
                            (SOME (boolSyntax.mk_neg formula)) theorem
                        in
                          raise CandidateSuccess theorem
                        end
                        handle ReplayFailure issue =>
                          if is_no_proof issue then ()
                          else raise ReplayFailure issue
                  in
                    (generate_candidates depth target (#next_origin context)
                       (#active context) (#active_origins context) attempt;
                     no_proof "universal replay" depth
                       "no candidate refuted the universal prefix")
                    handle CandidateSuccess theorem => theorem
                  end
                else if boolSyntax.is_exists formula then
                  let
                    val (variable, body) = boolSyntax.dest_exists formula
                    val avoids = base_avoids @ #active context @
                      Term.all_vars formula
                    val arbitrary = Term.variant avoids variable
                    val instance = Term.subst
                      [{redex = variable, residue = arbitrary}] body
                    val next : replay_context =
                      {active = #active context @ [arbitrary],
                       active_origins = #active_origins context @
                         [(arbitrary, SOME (#next_origin context))],
                       next_origin = #next_origin context + 1,
                       split_depths = #split_depths context @
                         [(arbitrary, 0)]}
                    val refutation = prove_neg instance next (depth + 1)
                    val generalized = Thm.GEN arbitrary refutation
                    val theorem = refute_exists "existential replay"
                      variable body generalized
                  in
                    require_theorem "existential replay" depth
                      (SOME (boolSyntax.mk_neg formula)) theorem
                  end
                else
                  case direct_leaf depth formula of
                      SOME theorem => theorem
                    | NONE =>
                        (case decision_leaf depth formula of
                             SOME theorem => theorem
                           | NONE => no_proof "leaf solving" depth
                               "the residual was not proved false")

              fun eligible_split variable =
                Term.free_in variable formula andalso
                depth_of (#split_depths context) variable <
                  #max_split_depth policy andalso
                Option.isSome (constructor_info (Term.type_of variable))

              fun case_split variable =
                let
                  val ty = Term.type_of variable
                  val variable_depth =
                    depth_of (#split_depths context) variable
                  val (info, constructors) =
                    valOf (constructor_info ty)
                  val nchotomy = TypeBasePure.nchotomy_of info
                  val nchotomy = require_theorem "datatype nchotomy" depth
                    NONE nchotomy
                  val branch_count = length constructors
                  val argument_count = List.foldl
                    (fn (constructor, total) =>
                      length (MFH.constructor_arg_types constructor) + total)
                    0 constructors
                  val _ =
                    if !case_branches + branch_count <=
                         #max_case_branches policy then ()
                    else no_proof "structural case split" depth
                      "case branch cap exhausted"
                  val _ = List.app (fn _ => charge
                    "case constructor argument" depth)
                    (List.tabulate (argument_count, fn index => index))
                  val split_theorem = Drule.ISPEC variable nchotomy
                  val split_theorem = require_theorem
                    "instantiated datatype nchotomy" depth NONE split_theorem

                  fun branch (assumptions, goal) =
                    let
                      val _ = case_branches := !case_branches + 1
                      val _ = charge "case branch" depth
                      val positive = boolSyntax.dest_neg goal
                      val frees = Term.free_vars_lr positive
                      fun old_depth candidate =
                        if Util.aconv_member candidate (#active context) then
                          depth_of (#split_depths context) candidate
                        else variable_depth + 1
                      val next : replay_context =
                        {active = frees,
                         active_origins = map (fn free =>
                           (free,
                            Option.join (Lib.op_assoc1 Term.aconv free
                              (#active_origins context)))) frees,
                         next_origin = #next_origin context,
                         split_depths = map (fn free =>
                           (free, old_depth free)) frees}
                      val theorem = prove_neg positive next (depth + 1)
                    in
                      Tactic.ACCEPT_TAC theorem (assumptions, goal)
                    end
                    handle Feedback.HOL_ERR _ =>
                      no_proof "structural case branch" depth
                        "generated branch did not match its replay theorem"

                  val tactic = Tactical.THEN
                    (Tactic.STRUCT_CASES_TAC split_theorem, branch)
                  val theorem = within_deadline
                    "structural case combination" depth
                    (fn () => Tactical.TAC_PROOF
                      (([], boolSyntax.mk_neg formula), tactic)) ()
                in
                  require_theorem "structural case combination" depth
                    (SOME (boolSyntax.mk_neg formula)) theorem
                end

              fun try_cases [] = no_proof "structural case split" depth
                    "no exhaustive split closed every branch"
                | try_cases (variable :: rest) =
                    (case_split variable
                     handle ReplayFailure issue =>
                       if is_no_proof issue then try_cases rest
                       else raise ReplayFailure issue)

              fun induction variable =
                let
                  val ty = Term.type_of variable
                  val (_, constructors) = valOf (constructor_info ty)
                  val _ =
                    if quantifier_free formula then ()
                    else no_proof "structural induction" depth
                      "residual formula is not quantifier-free"
                  val _ =
                    if regular_recursive_type ty constructors then ()
                    else no_proof "structural induction" depth
                      "datatype is nonrecursive, mutual, or nested"
                  val induction_theorem = TypeBase.induction_of ty
                    handle Feedback.HOL_ERR _ => no_proof
                      "structural induction" depth
                      "datatype has no induction theorem"
                  val induction_theorem = require_theorem
                    "datatype induction theorem" depth NONE induction_theorem
                  val _ =
                    if single_property_induction ty induction_theorem then ()
                    else no_proof "structural induction" depth
                      "induction theorem is not single-property"
                  val _ =
                    if !induction_attempts < #max_inductions policy then ()
                    else no_proof "structural induction" depth
                      "induction attempt cap exhausted"
                  val _ = induction_attempts := !induction_attempts + 1
                  val _ = charge "structural induction" depth
                  val generalized = boolSyntax.mk_forall
                    (variable, boolSyntax.mk_neg formula)
                  val tactic = Tactical.THEN
                    (Tactic.HO_MATCH_MP_TAC induction_theorem,
                     local_induction_tactic depth)
                  val theorem = within_deadline
                    "structural induction" depth
                    (fn () => Tactical.TAC_PROOF
                      (([], generalized), tactic)) ()
                    handle Feedback.HOL_ERR _ => no_proof
                      "structural induction" depth
                      "a constructor obligation remained open"
                  val theorem = require_theorem
                    "completed structural induction" depth
                    (SOME generalized) theorem
                  val specialized = Drule.ISPEC variable theorem
                in
                  require_theorem "structural induction specialization"
                    depth (SOME (boolSyntax.mk_neg formula)) specialized
                end

              fun try_inductions [] = no_proof "structural induction" depth
                    "no admitted induction closed every constructor premise"
                | try_inductions (variable :: rest) =
                    if not (Term.free_in variable formula) orelse
                       not (Option.isSome
                         (constructor_info (Term.type_of variable))) then
                      try_inductions rest
                    else
                      (induction variable
                       handle ReplayFailure issue =>
                         if is_no_proof issue then try_inductions rest
                         else raise ReplayFailure issue)

              fun strategies () =
                (ordinary ()
                 handle ReplayFailure issue =>
                   if not (is_no_proof issue) then raise ReplayFailure issue
                   else if #enable_cases policy then
                     (try_cases (List.filter eligible_split
                        (#active context))
                      handle ReplayFailure case_issue =>
                        if not (is_no_proof case_issue) then
                          raise ReplayFailure case_issue
                        else if #enable_induction policy then
                          try_inductions (#active context)
                        else raise ReplayFailure issue)
                   else if #enable_induction policy then
                     try_inductions (#active context)
                   else raise ReplayFailure issue)
            in
              strategies ()
              handle ReplayFailure issue =>
                if is_no_proof issue then
                  (remember current; raise ReplayFailure issue)
                else raise ReplayFailure issue
            end

          val initial_context : replay_context =
            {active = [], active_origins = [], next_origin = 0,
             split_depths = []}
          val replayed = prove_neg pnf initial_context 0
          val certificate = undo_normalization "model replay"
            (normalized_equality, prenex_equality) replayed
          val certificate = conform_conclusion
            "model replay" expected certificate
          val certificate = require_theorem "final certificate audit" 0
            (SOME expected) certificate
        in
          Certified certificate
        end

      fun snapshot issue : diagnostics =
        {nodes = !nodes,
         ordinary_bindings = !ordinary_bindings,
         reconstructed_hints = !reconstructed_hints,
         active_candidates = !active_candidates,
         applications = !applications,
         constructor_terms = !constructor_terms,
         generated_candidates = !generated_candidates,
         function_states = !function_states,
         attempted_candidates = !attempted_candidates,
         memo_hits = !memo_hits,
         case_branches = !case_branches,
         induction_attempts = !induction_attempts,
         leaf_attempts = !leaf_attempts,
         real_arith_attempts = !real_arith_attempts,
         schematic_attempts = 0,
         completion_attempts = 0,
         candidate_trace = rev (!candidate_trace),
         consumed_fuel = #total_fuel policy - !remaining,
         elapsed = Time.- (Time.now (), start),
         failure = issue}

      val reported_failure = ref (NONE : failure option)
      val outcome =
        ((case if #enable_whole_formula policy then whole_formula ()
               else NONE of
              SOME answer => answer
            | NONE => replay_pnf ())
         handle Interrupt => raise Interrupt
              | ReplayFailure issue =>
                  (reported_failure := SOME issue;
                   NoCertificate (render_failure issue))
              | error =>
                  let val issue =
                    {kind = InternalFailure,
                     stage = "public boundary",
                     depth = 0,
                     detail = replay_error_text error}
                  in
                    reported_failure := SOME issue;
                    NoCertificate (render_failure issue)
                  end)
    in
      (outcome, snapshot (!reported_failure))
    end

  fun policy_with_resources (policy : policy)
        {fuel, generated, attempted, function_states, cases, inductions}
        : policy =
    {total_fuel = Int.max (0, fuel),
     max_generated_candidates = Int.max (0,
       #max_generated_candidates policy - generated),
     max_attempted_candidates = Int.max (0,
       #max_attempted_candidates policy - attempted),
     max_completion_candidates = #max_completion_candidates policy,
     max_completion_vectors = #max_completion_vectors policy,
     max_function_states = Int.max (0,
       #max_function_states policy - function_states),
     max_constructor_depth = #max_constructor_depth policy,
     max_constructor_width = #max_constructor_width policy,
     max_constructor_size = #max_constructor_size policy,
     max_split_depth = #max_split_depth policy,
     max_case_branches = Int.max (0, #max_case_branches policy - cases),
     max_inductions = Int.max (0, #max_inductions policy - inductions),
     max_leaf_rounds = #max_leaf_rounds policy,
     enable_whole_formula = #enable_whole_formula policy,
     enable_cases = #enable_cases policy,
     enable_induction = #enable_induction policy,
     enable_synthesis = #enable_synthesis policy,
     enable_taut = #enable_taut policy,
     enable_omega = #enable_omega policy,
     enable_real_arith = #enable_real_arith policy}

  fun add_diagnostics (left : diagnostics) (right : diagnostics) issue
        schematic_attempts completion_attempts : diagnostics =
    {nodes = #nodes left + #nodes right,
     ordinary_bindings = #ordinary_bindings left +
       #ordinary_bindings right,
     reconstructed_hints = #reconstructed_hints left +
       #reconstructed_hints right,
     active_candidates = #active_candidates left + #active_candidates right,
     applications = #applications left + #applications right,
     constructor_terms = #constructor_terms left + #constructor_terms right,
     generated_candidates = #generated_candidates left +
       #generated_candidates right,
     function_states = #function_states left + #function_states right,
     attempted_candidates = #attempted_candidates left +
       #attempted_candidates right,
     memo_hits = #memo_hits left + #memo_hits right,
     case_branches = #case_branches left + #case_branches right,
     induction_attempts = #induction_attempts left +
       #induction_attempts right,
     leaf_attempts = #leaf_attempts left + #leaf_attempts right,
     real_arith_attempts = #real_arith_attempts left +
       #real_arith_attempts right,
     schematic_attempts = schematic_attempts,
     completion_attempts = completion_attempts,
     candidate_trace = #candidate_trace left @ #candidate_trace right,
     consumed_fuel = #consumed_fuel left + #consumed_fuel right,
     elapsed = Time.+ (#elapsed left, #elapsed right),
     failure = issue}

  fun set_attempt_counts (stats : diagnostics) schematic completion issue =
    {nodes = #nodes stats,
     ordinary_bindings = #ordinary_bindings stats,
     reconstructed_hints = #reconstructed_hints stats,
     active_candidates = #active_candidates stats,
     applications = #applications stats,
     constructor_terms = #constructor_terms stats,
     generated_candidates = #generated_candidates stats,
     function_states = #function_states stats,
     attempted_candidates = #attempted_candidates stats,
     memo_hits = #memo_hits stats,
     case_branches = #case_branches stats,
     induction_attempts = #induction_attempts stats,
     leaf_attempts = #leaf_attempts stats,
     real_arith_attempts = #real_arith_attempts stats,
     schematic_attempts = schematic,
     completion_attempts = completion,
     candidate_trace = #candidate_trace stats,
     consumed_fuel = #consumed_fuel stats,
     elapsed = #elapsed stats,
     failure = issue}

  (* Multiple completion attempts are budgeted by passing only the remaining
     fuel to each single-attempt replay.  The absolute deadline is unchanged,
     so neither resource can reset between candidates. *)
  fun certify_portfolio_detailed_rich
        {original, env, hints, holes, policy, deadline} =
    let
      val remaining = ref (#total_fuel policy)
      val completion_attempts = ref 0
      val completion_overhead = ref 0
      val used_generated = ref 0
      val used_attempted = ref 0
      val used_function_states = ref 0
      val used_cases = ref 0
      val used_inductions = ref 0

      fun run env hints =
        let
          val answer = certify_detailed_rich
            {original = original, env = env, hints = hints,
             policy = policy_with_resources policy
               {fuel = !remaining, generated = !used_generated,
                attempted = !used_attempted,
                function_states = !used_function_states,
                cases = !used_cases, inductions = !used_inductions},
             deadline = deadline}
          val _ = remaining := Int.max (0,
            !remaining - #consumed_fuel (#2 answer))
          val _ = used_generated := !used_generated +
            #generated_candidates (#2 answer)
          val _ = used_attempted := !used_attempted +
            #attempted_candidates (#2 answer)
          val _ = used_function_states := !used_function_states +
            #function_states (#2 answer)
          val _ = used_cases := !used_cases + #case_branches (#2 answer)
          val _ = used_inductions := !used_inductions +
            #induction_attempts (#2 answer)
        in
          answer
        end

      val (schematic_result, schematic_stats0) = run env hints
      (* [null holes] below means "every env value is closed", not just "no
         hole was declared" - callers (e.g. [certification_env_with_holes])
         must drop, never authorize, a binding with a stray free variable
         when it declares no matching hole. *)
      val schematic_kind =
        case schematic_result of
            DiscardedByWholeFormulaEval => Exact
          | _ => if null holes then Exact else Schematic
      val schematic_stats = set_attempt_counts schematic_stats0 1 0
        (#failure schematic_stats0)

      fun resource_failure stats =
        case #failure stats of
            SOME {kind = FuelExhausted, ...} => true
          | SOME {kind = DeadlineExhausted, ...} => true
          | _ => false

      fun attempt_outcome Exact result = result
        | attempt_outcome Schematic DiscardedByWholeFormulaEval =
            NoCertificate "schematic completion evaluated true"
        | attempt_outcome ChosenCompletion DiscardedByWholeFormulaEval =
            NoCertificate "chosen completion evaluated true"
        | attempt_outcome _ result = result

      val pool = map #2 env @ map #term (hints : replay_hint list)
      fun hole_free tm = null (Term.free_vars_lr tm)
      val closed_pool = List.filter hole_free pool
      val raw_resolve = constructor_resolver ()
      fun completion_constructors ty =
        if MFH.is_codatatype ty then NONE else raw_resolve ty

      fun candidates ty depth =
        let
          val limit = #max_completion_candidates policy
          val values = ref ([] : term list)
          fun add tm =
            if length (!values) >= limit orelse
               not (Util.same_type ty (Term.type_of tm)) orelse
               not (hole_free tm) orelse
               candidate_size tm > #max_constructor_size policy orelse
               Util.aconv_member tm (!values)
            then ()
            else if !remaining <= 0 then ()
            else
              (remaining := !remaining - 1;
               completion_overhead := !completion_overhead + 1;
               values := !values @ [tm])
          val generated = synth_values_bounded
            {target = ty, pool = closed_pool, active = [],
             max_depth = depth, width = limit,
             max_size = #max_constructor_size policy,
             resolve = completion_constructors, charge = fn () => ()}
          val _ = List.app add generated
          val _ =
            case Lib.total Type.dom_rng ty of
                SOME (domain_ty, range_ty) =>
                  List.app (fn value => add
                    (combinSyntax.mk_K_1 (value, domain_ty)))
                    (candidates range_ty (Int.max (0, depth - 1)))
              | NONE => ()
          val _ = add (boolSyntax.mk_arb ty)
        in
          !values
        end

      val choices = map (fn hole =>
        candidates (Term.type_of hole) (#max_constructor_depth policy)) holes
      val vectors = ref ([] : term list list)
      val vector_limit = #max_completion_vectors policy
      fun same_vector (left, right) =
        length left = length right andalso
        ListPair.allEq (fn (first, second) => Term.aconv first second)
          (left, right)
      fun add_vector vector =
        if length (!vectors) >= vector_limit orelse
           List.exists (fn old => same_vector (old, vector)) (!vectors)
        then ()
        else vectors := !vectors @ [vector]
      val diagonal_count =
        if null choices then 0
        else List.foldl Int.min vector_limit (map length choices)
      val _ = List.app (fn index =>
        add_vector (map (fn options => List.nth (options, index)) choices))
        (List.tabulate (diagonal_count, fn index => index))
      val _ = ignore (app_combinations_bounded
        vector_limit add_vector choices)

      fun substitute substitutions tm = Term.subst substitutions tm
      fun completed_inputs vector =
        let
          val substitutions = ListPair.mapEq (fn (hole, value) =>
            {redex = hole, residue = value}) (holes, vector)
          val env = map (fn (left, right) =>
            (left, substitute substitutions right)) env
          val hints = map (fn
            ({term, source, provenance} : replay_hint) =>
              {term = substitute substitutions term,
               source = source, provenance = provenance}) hints
        in
          (env, hints)
        end

      fun combine accumulated next =
        add_diagnostics accumulated next (#failure next) 1
          (!completion_attempts)

      fun with_overhead (stats : diagnostics) : diagnostics =
        {nodes = #nodes stats,
         ordinary_bindings = #ordinary_bindings stats,
         reconstructed_hints = #reconstructed_hints stats,
         active_candidates = #active_candidates stats,
         applications = #applications stats,
         constructor_terms = #constructor_terms stats,
         generated_candidates = #generated_candidates stats,
         function_states = #function_states stats,
         attempted_candidates = #attempted_candidates stats,
         memo_hits = #memo_hits stats,
         case_branches = #case_branches stats,
         induction_attempts = #induction_attempts stats,
         leaf_attempts = #leaf_attempts stats,
         real_arith_attempts = #real_arith_attempts stats,
         schematic_attempts = #schematic_attempts stats,
         completion_attempts = #completion_attempts stats,
         candidate_trace = #candidate_trace stats,
         consumed_fuel = #consumed_fuel stats + !completion_overhead,
         elapsed = #elapsed stats,
         failure = #failure stats}

      fun search [] stats =
            (NoCertificate
               "model replay exhausted bounded hole completions",
             with_overhead (set_attempt_counts stats 1
               (!completion_attempts) (#failure stats)))
        | search (vector :: rest) stats =
            if !remaining <= 0 then
              (NoCertificate "model replay fuel exhausted",
               with_overhead stats)
            else
              let
                val _ = remaining := !remaining - 1
                val _ = completion_overhead := !completion_overhead + 1
                val _ = completion_attempts := !completion_attempts + 1
                val (completed_env, completed_hints) =
                  completed_inputs vector
                val (raw_result, attempt_stats) =
                  run completed_env completed_hints
                val result = attempt_outcome ChosenCompletion raw_result
                val stats = combine stats attempt_stats
              in
                case result of
                    Certified theorem =>
                      (Certified theorem, with_overhead stats)
                  | DiscardedByWholeFormulaEval => search rest stats
                  | NoCertificate _ =>
                      if resource_failure attempt_stats then
                        (result, with_overhead stats)
                      else search rest stats
              end
    in
      case schematic_result of
          Certified _ =>
            (attempt_outcome schematic_kind schematic_result,
             schematic_stats)
        | DiscardedByWholeFormulaEval =>
            (* The single-attempt engine returns this only when the
               instantiated formula is hole-free, hence exact. *)
            (attempt_outcome schematic_kind schematic_result,
             schematic_stats)
        | NoCertificate _ =>
            if null holes orelse resource_failure schematic_stats0 then
              (schematic_result, schematic_stats)
            else
              search (!vectors) schematic_stats
    end

  fun direct_hint term : replay_hint =
    {term = term, source = DirectHint, provenance = NONE}

  fun certify_detailed {original, env, hints, policy, deadline} =
    certify_detailed_rich
      {original = original, env = env, hints = map direct_hint hints,
       policy = policy, deadline = deadline}

  fun certify_with_policy arguments = #1 (certify_detailed arguments)

  fun certify {original, env, hints, fuel, deadline} =
    certify_with_policy
      {original = original, env = env, hints = hints,
       policy = default_policy fuel, deadline = deadline}
end
