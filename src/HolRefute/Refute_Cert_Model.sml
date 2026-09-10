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
     max_leaf_rounds : int}

  type diagnostics =
    {generated_candidates : int,
     function_states : int,
     attempted_candidates : int,
     case_branches : int,
     induction_attempts : int,
     schematic_attempts : int,
     completion_attempts : int,
     candidate_trace : (int * term * term) list,
     consumed_fuel : int,
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
     max_leaf_rounds = 2}

  fun failure_kind_name NoProof = "no-proof"
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

  fun resource_failure ({kind, ...} : failure) =
    kind = DeadlineExhausted orelse kind = FuelExhausted

  fun theorem_acceptable expected theorem =
    null (Thm.hyp theorem) andalso trusted theorem andalso
    (case expected of
         NONE => true
       | SOME conclusion => Term.aconv (Thm.concl theorem) conclusion)

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

  (* Every replay attempt of one portfolio run charges the same counters,
     so each is compared against its [policy] ceiling directly and no
     attempt can respend what an earlier one spent. *)
  type budget =
    {remaining : int ref,
     generated_candidates : int ref,
     function_states : int ref,
     attempted_candidates : int ref,
     case_branches : int ref,
     induction_attempts : int ref,
     schematic_attempts : int ref,
     completion_attempts : int ref,
     candidate_trace : (int * term * term) list ref}

  fun new_budget (policy : policy) : budget =
    {remaining = ref (#total_fuel policy),
     generated_candidates = ref 0,
     function_states = ref 0,
     attempted_candidates = ref 0,
     case_branches = ref 0,
     induction_attempts = ref 0,
     schematic_attempts = ref 0,
     completion_attempts = ref 0,
     candidate_trace = ref []}

  fun budget_diagnostics (policy : policy) (budget : budget) issue
        : diagnostics =
    {generated_candidates = ! (#generated_candidates budget),
     function_states = ! (#function_states budget),
     attempted_candidates = ! (#attempted_candidates budget),
     case_branches = ! (#case_branches budget),
     induction_attempts = ! (#induction_attempts budget),
     schematic_attempts = ! (#schematic_attempts budget),
     completion_attempts = ! (#completion_attempts budget),
     candidate_trace = rev (! (#candidate_trace budget)),
     consumed_fuel = #total_fuel policy - ! (#remaining budget),
     failure = issue}

  fun certify_detailed_rich
        {original, env, hints, policy, budget, deadline} =
    let
      val hint_terms = map #term (hints : replay_hint list)
      val {remaining, generated_candidates, function_states,
           attempted_candidates, case_branches, induction_attempts,
           candidate_trace, ...} = budget : budget

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
        case portfolio depth formula of
            SOME theorem =>
              if Term.aconv (rhs_of theorem) boolSyntax.F then
                SOME (require_theorem "leaf equality elimination" depth
                  (SOME (boolSyntax.mk_neg formula))
                  (Drule.EQF_ELIM theorem))
              else NONE
          | NONE => NONE

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
            [(true, "propositional leaf", tautLib.TAUT_CONV),
             (true, "Presburger leaf", Omega.OMEGA_CONV),
             (mentions_real goal,
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

          fun quantifier_free tm =
            not (Lib.can (HolKernel.find_term is_quantifier) tm)
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
             split_depths : int list}

          (* Keyed on the abstracted formula alone: Term.compare is the
             alpha-equivalence order that same_state's own aconv test uses,
             so states that same_state identifies always share a bucket. *)
          val failed = ref
            (Redblackmap.mkDict Term.compare :
              (term, failed_state list) Redblackmap.dict)

          fun abstract active tm = Term.list_mk_abs (active, tm)
          fun same_types (left, right) =
            ListPair.allEq (fn (a, b) => Util.same_type a b) (left, right)
          fun depth_of rows variable =
            Option.getOpt (Lib.op_assoc1 Term.aconv variable rows, 0)
          fun state formula
                ({active, split_depths, ...} : replay_context)
                : failed_state =
            {formula = abstract active formula,
             active_types = map Term.type_of active,
             split_depths = map (depth_of split_depths) active}
          fun same_state (left : failed_state) (right : failed_state) =
            Term.aconv (#formula left) (#formula right) andalso
            same_types (#active_types left, #active_types right) andalso
            #split_depths left = #split_depths right
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

          fun emit_candidate seen_terms attempt term =
            if HOLset.member (!seen_terms, term) then ()
            else if !generated_candidates >=
                    #max_generated_candidates policy then
              ()
            else
              (generated_candidates := !generated_candidates + 1;
               seen_terms := HOLset.add (!seen_terms, term);
               attempt term)

          fun generate_candidates depth target target_origin active
                active_origins attempt =
            let
              val seen_terms = ref (HOLset.empty Term.compare)
              fun emit term = emit_candidate seen_terms attempt term

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

              fun emit_hint ({term, ...} : replay_hint) = emit term

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
                                     emit applied
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
                                    emit applied
                                  else ()
                              | NONE => ()))
                | provenance_application _ = ()

              fun synthesized () =
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
                    List.app emit new
                  end
            in
              List.app emit_hint
                (List.filter (fn
                  ({provenance = SOME metadata, ...} : replay_hint) =>
                    #origin metadata = SOME target_origin
                  | _ => false) direct_skolems);
              List.app emit direct_bindings;
              List.app emit_hint direct_skolems;
              (* [DirectHint] (an explicitly-supplied targeted hint, e.g.
                 the real-Frac literal) before [TypeValue] (bulk type
                 enumeration): a targeted hint must not be starved by
                 [max_generated_candidates] behind same-typed filler. *)
              List.app emit_hint direct_generic;
              List.app emit_hint direct_types;
              List.app emit direct_active;
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
              val taut_goal = Tactical.TRY tautLib.ASM_TAUT_TAC
              val omega_goal = Tactical.TRY Omega.OMEGA_TAC
              (* Unlike [decision_leaf]'s single-formula gate,
                 [REAL_ASM_ARITH_TAC] consumes assumptions too, so the
                 gate must see the whole goal - every assumption plus the
                 conclusion - not the conclusion alone. *)
              fun real_goal (goal as (asl, w)) =
                if List.exists mentions_real (w :: asl)
                then Tactical.TRY realLib.REAL_ASM_ARITH_TAC goal
                else Tactical.ALL_TAC goal
              fun account goal =
                (charge "induction constructor obligation" depth;
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
              val current = state formula context
              val _ = if seen current then
                  no_proof "memoization" depth
                    "state already failed with these strategy permissions"
                else ()

              fun ordinary () =
                if boolSyntax.is_forall formula then
                  let
                    val (variable, body) = boolSyntax.dest_forall formula
                    val target = Term.type_of variable

                    fun attempt witness =
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
                   else
                     (try_cases (List.filter eligible_split
                        (#active context))
                      handle ReplayFailure case_issue =>
                        if not (is_no_proof case_issue) then
                          raise ReplayFailure case_issue
                        else try_inductions (#active context)))
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

      val reported_failure = ref (NONE : failure option)
      val outcome =
        ((case whole_formula () of
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
      (outcome, budget_diagnostics policy budget (!reported_failure))
    end

  (* Every completion attempt shares the run's [budget] and the absolute
     deadline, so neither resource can reset between candidates.  Each
     attempt's diagnostics are therefore the run's totals to that point,
     including the fuel the portfolio itself spends below. *)
  fun certify_portfolio_detailed_rich
        {original, env, hints, holes, policy, deadline} =
    let
      val budget = new_budget policy
      val remaining = #remaining budget
      val completion_attempts = #completion_attempts budget

      fun run env hints =
        certify_detailed_rich
          {original = original, env = env, hints = hints,
           policy = policy, budget = budget, deadline = deadline}

      (* The schematic attempt is made once, ahead of any completion. *)
      val _ = #schematic_attempts budget := 1
      val (schematic_result, schematic_stats) = run env hints
      (* [null holes] below means "every env value is closed", not just "no
         hole was declared" - callers (e.g. [certification_env_with_holes])
         must drop, never authorize, a binding with a stray free variable
         when it declares no matching hole. *)
      val schematic_kind =
        case schematic_result of
            DiscardedByWholeFormulaEval => Exact
          | _ => if null holes then Exact else Schematic

      fun resource_exhausted (stats : diagnostics) =
        case #failure stats of
            SOME issue => resource_failure issue
          | NONE => false

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

      fun completed_inputs vector =
        let
          val substitute = Term.subst (ListPair.mapEq (fn (hole, value) =>
            {redex = hole, residue = value}) (holes, vector))
          val env = map (fn (left, right) =>
            (left, substitute right)) env
          val hints = map (fn
            ({term, source, provenance} : replay_hint) =>
              {term = substitute term,
               source = source, provenance = provenance}) hints
        in
          (env, hints)
        end

      (* Diagnostics always come from the shared budget, so [search] need
         only carry the failure the last attempt reported. *)
      fun search [] issue =
            (NoCertificate
               "model replay exhausted bounded hole completions",
             budget_diagnostics policy budget issue)
        | search (vector :: rest) issue =
            if !remaining <= 0 then
              (NoCertificate "model replay fuel exhausted",
               budget_diagnostics policy budget issue)
            else
              let
                val _ = remaining := !remaining - 1
                val _ = completion_attempts := !completion_attempts + 1
                val (completed_env, completed_hints) =
                  completed_inputs vector
                val (raw_result, attempt_stats) =
                  run completed_env completed_hints
                val result = attempt_outcome ChosenCompletion raw_result
              in
                case result of
                    Certified theorem => (Certified theorem, attempt_stats)
                  | DiscardedByWholeFormulaEval =>
                      search rest (#failure attempt_stats)
                  | NoCertificate _ =>
                      if resource_exhausted attempt_stats then
                        (result, attempt_stats)
                      else search rest (#failure attempt_stats)
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
            if null holes orelse resource_exhausted schematic_stats then
              (schematic_result, schematic_stats)
            else
              search (!vectors) (#failure schematic_stats)
    end
end
