structure Refute_Cert_Model = struct
  open Refute_Cert
  structure Util = Refute_Util
  structure MFH = Refute_ModelFinder_HOL

  datatype result =
      Certified of Thm.thm
    | NoCertificate of string
    | DiscardedByWholeFormulaEval

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

  type dependency =
    {origin : int,
     source_type : Type.hol_type}
  type provenance =
    {origin : int,
     source_type : Type.hol_type,
     positive : bool,
     dependencies : dependency list,
     nickname : string,
     stage : string}
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
     enable_omega : bool}

  type diagnostics =
    {nodes : int,
     ordinary_bindings : int,
     reconstructed_hints : int,
     active_candidates : int,
     applications : int,
     constructor_terms : int,
     attempted_candidates : int,
     memo_hits : int,
     case_branches : int,
     induction_attempts : int,
     leaf_attempts : int,
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
     enable_omega = true}

  fun policy_for_test
        {fuel, cases, induction, synthesis, taut, omega,
         split_depth, branches, constructor_depth, constructor_width} :
        policy =
    {total_fuel = Int.max (0, fuel),
     max_generated_candidates = replay_candidate_limit,
     max_attempted_candidates = replay_candidate_limit,
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
     enable_omega = omega}

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

      fun beta depth tm =
        optional_equality "leaf beta/let normalization" depth tm
          (Conv.DEPTH_CONV Thm.BETA_CONV)

      fun cbv depth tm =
        optional_equality "leaf CBV evaluation" depth tm eval_original

      fun simplify depth tm =
        optional_equality "leaf simplification" depth tm
          (simpLib.SIMP_CONV (BasicProvers.srw_ss ()) [])

      fun decisive theorem =
        let val rhs = rhs_of theorem
        in
          Term.aconv rhs boolSyntax.T orelse
          Term.aconv rhs boolSyntax.F
        end

      fun compose stage depth first second =
        let
          val middle = rhs_of first
          val left = #1 (boolSyntax.dest_eq (Thm.concl second))
          val _ = if Term.aconv middle left then () else
            fail InternalFailure stage depth
              "conversion endpoints do not agree"
          val theorem = Thm.TRANS first second
        in
          require_theorem stage depth
            (SOME (boolSyntax.mk_eq
              (#1 (boolSyntax.dest_eq (Thm.concl first)), rhs_of second)))
            theorem
        end

      fun equality_portfolio depth tm =
        let
          val seen = ref ([] : term list)
          fun repeated candidate = Util.aconv_member candidate (!seen)
          fun one conversion theorem =
            case conversion depth (rhs_of theorem) of
                NONE => theorem
              | SOME next =>
                  if Term.aconv (rhs_of next) (rhs_of theorem) then theorem
                  else compose "leaf conversion composition" depth
                    theorem next
          fun round 0 theorem = theorem
            | round count theorem =
                let
                  val current = rhs_of theorem
                  val _ = seen := current :: !seen
                  val theorem = one cbv theorem
                  val theorem = one simplify theorem
                  val theorem = one cbv theorem
                  val next = rhs_of theorem
                in
                  if decisive theorem orelse Term.aconv current next orelse
                     repeated next then theorem
                  else round (count - 1) theorem
                end
          val initial =
            case beta depth tm of
                SOME theorem => theorem
              | NONE => Thm.REFL tm
          val theorem = round (#max_leaf_rounds policy) initial
        in
          if theorem_acceptable
               (SOME (boolSyntax.mk_eq (tm, rhs_of theorem))) theorem
          then SOME theorem
          else NONE
        end

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
          case equality_portfolio depth formula of
              SOME theorem =>
                if Term.aconv (rhs_of theorem) boolSyntax.F then
                  SOME (require_theorem "leaf equality elimination" depth
                    (SOME (boolSyntax.mk_neg formula))
                    (Drule.EQF_ELIM theorem))
                else NONE
            | NONE => NONE
        end

      fun decision_leaf depth formula =
        let val goal = boolSyntax.mk_neg formula
        in
          case if #enable_taut policy then
                 prove_by_conversion "propositional leaf" depth
                   tautLib.TAUT_CONV goal
               else NONE of
              SOME theorem => SOME theorem
            | NONE =>
                if #enable_omega policy then
                  prove_by_conversion "Presburger leaf" depth
                    Omega.OMEGA_CONV goal
                else NONE
        end

      val (variables, closure, body) = closure_of original
      val expected = boolSyntax.mk_neg closure
      val instance = instantiate env body

      fun fast_certificate theorem =
        let
          val negated_instance = Drule.EQF_ELIM theorem
          val assumed = Thm.ASSUME closure
          val witnesses = map (instantiate env) variables
          val assumed_instance = Drule.SPECL witnesses assumed
          val falsehood = Thm.MP (Thm.NOT_ELIM negated_instance)
            assumed_instance
          val certificate = Thm.NOT_INTRO
            (Thm.DISCH closure falsehood)
          val certificate = conform_conclusion
            "whole-formula replay" expected certificate
        in
          require_theorem "whole-formula replay" 0
            (SOME expected) certificate
        end

      fun whole_formula () =
        case equality_portfolio 0 instance of
            SOME theorem =>
              if Term.aconv (rhs_of theorem) boolSyntax.F then
                SOME (Certified (fast_certificate theorem))
              else if Term.aconv (rhs_of theorem) boolSyntax.T andalso
                      null (Term.free_vars_lr instance) then
                SOME DiscardedByWholeFormulaEval
              else NONE
          | NONE => NONE

      fun replay_pnf () =
        let
          val _ = charge "normalization" 0
          val normalized_equality = within_deadline "normalization" 0
            (fn tm =>
              Ho_Rewrite.REWRITE_CONV Refute_Core.normal_rewrites tm
              handle Conv.UNCHANGED => Thm.REFL tm) closure
          val normalized_equality = require_theorem "normalization" 0
            (SOME (boolSyntax.mk_eq
              (closure, rhs_of normalized_equality))) normalized_equality
          val normalized = rhs_of normalized_equality
          val _ = charge "prenex conversion" 0
          val prenex_equality = within_deadline "prenex conversion" 0
            (fn tm => Refute_Narrow.prenex_conversion tm
              handle Conv.UNCHANGED => Thm.REFL tm) normalized
          val prenex_equality = require_theorem "prenex conversion" 0
            (SOME (boolSyntax.mk_eq
              (normalized, rhs_of prenex_equality))) prenex_equality
          val pnf = rhs_of prenex_equality

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

          (* is_codatatype walks the theory ancestry and cinst rebuilds
             every constructor, but a replay revisits the same handful of
             types on every node, so the resolution is memoized. *)
          val constructor_cache = ref
            (Redblackmap.mkDict Type.compare :
              (Type.hol_type,
               (TypeBasePure.tyinfo * term list) option) Redblackmap.dict)

          fun resolve_constructors ty =
            if MFH.is_codatatype ty then NONE
            else
              case TypeBase.fetch ty of
                  NONE => NONE
                | SOME info =>
                    let val constructors = map (TypeBasePure.cinst ty)
                      (TypeBasePure.constructors_of info)
                    in if null constructors then NONE
                       else SOME (info, constructors)
                    end
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

          fun candidate_size tm =
            let fun size candidate =
              let val (_, arguments) = boolSyntax.strip_comb candidate
              in 1 + List.foldl (fn (argument, total) =>
                   size argument + total) 0 arguments
              end
            in size tm end

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

          fun pool_terms target active =
            List.filter (fn candidate =>
              Util.same_type target (Term.type_of candidate))
              (pool_base @ active)

          fun synth_values target active max_depth =
            let
              (* Held in reverse and reversed on exit: emission order
                 decides which witness is tried first. *)
              val values = ref (rev (pool_terms target active))
              val count = ref (length (!values))
              val width = #max_constructor_width policy

              fun add value =
                if !count >= width orelse
                   candidate_size value > #max_constructor_size policy orelse
                   Util.aconv_member value (!values)
                then ()
                else (values := value :: !values; count := !count + 1)

              fun build depth =
                    (case constructor_info target of
                         NONE => ()
                       | SOME (_, constructors) =>
                           let
                             fun one constructor =
                               let
                                 val argument_types =
                                   MFH.constructor_arg_types constructor
                                 val choices =
                                   if depth <= 0 andalso
                                      not (null argument_types) then []
                                   else map (fn ty =>
                                     synth_values ty active (depth - 1))
                                     argument_types
                                 fun emit arguments =
                                   let
                                     val term = Term.list_mk_comb
                                       (constructor, arguments)
                                     val _ = charge
                                       "constructor synthesis" 0
                                   in add term end
                               in
                                 if null argument_types then add constructor
                                 else if depth <= 0 then ()
                                 else if List.exists null choices then ()
                                 else ignore (app_combinations_bounded
                                   width emit choices)
                               end
                           in
                             List.app one constructors
                           end)
            in
              build max_depth;
              rev (!values)
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
                    if #origin metadata <> target_origin then ()
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
                    val generated = synth_values target active
                      (#max_constructor_depth policy)
                    val new = List.filter (fn term =>
                      not (Util.aconv_member term known)) generated
                  in
                    emit_terms SynthesizedConstructor new
                  end
            in
              List.app (emit_hint ReconstructedSkolem)
                (List.filter (fn
                  ({provenance = SOME metadata, ...} : replay_hint) =>
                    #origin metadata = target_origin
                  | _ => false) direct_skolems);
              emit_terms OrdinaryBinding direct_bindings;
              List.app (emit_hint ReconstructedSkolem) direct_skolems;
              List.app (emit_hint ReconstructedTypeValue) direct_types;
              List.app (emit_hint GenericHint) direct_generic;
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
              fun account goal =
                (charge "induction constructor obligation" depth;
                 leaf_attempts := !leaf_attempts + 1;
                 Tactical.EVERY
                   [introductions, simplify_goal, assumptions,
                    simplify_goal, taut_goal, omega_goal]
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
                          val assumed = Thm.ASSUME formula
                          val assumed_instance =
                            Drule.SPECL [witness] assumed
                          val falsehood = Thm.MP
                            (Thm.NOT_ELIM refutation) assumed_instance
                          val theorem = Thm.NOT_INTRO
                            (Thm.DISCH formula falsehood)
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
                    val conversion = Conv.CONV_RULE
                      (Conv.DEPTH_CONV Thm.BETA_CONV)
                      (Drule.ISPEC (Term.mk_abs (variable, body))
                        boolTheory.NOT_EXISTS_THM)
                    val conversion = require_theorem
                      "existential conversion" depth NONE conversion
                    val target = rhs_of conversion
                    val generalized = conform_conclusion
                      "existential replay" target generalized
                    val theorem = Thm.EQ_MP
                      (Thm.SYM conversion) generalized
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
          val prenex_negated_equality =
            Thm.AP_TERM boolSyntax.negation prenex_equality
          val replayed = conform_conclusion
            "prenex replay" (rhs_of prenex_negated_equality) replayed
          val normalized_certificate = Thm.EQ_MP
            (Thm.SYM prenex_negated_equality) replayed
          val normalized_negated_equality =
            Thm.AP_TERM boolSyntax.negation normalized_equality
          val certificate = Thm.EQ_MP
            (Thm.SYM normalized_negated_equality) normalized_certificate
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
         attempted_candidates = !attempted_candidates,
         memo_hits = !memo_hits,
         case_branches = !case_branches,
         induction_attempts = !induction_attempts,
         leaf_attempts = !leaf_attempts,
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
