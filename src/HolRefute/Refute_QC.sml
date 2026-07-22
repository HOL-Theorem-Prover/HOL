structure Refute_QC = struct
  type term = Term.term
  open Refute_Cert Refute_Eval
  structure SmartGen = Refute_SmartGen
  structure MFH = Refute_ModelFinder_HOL

  fun member tm = List.exists (fn other => Term.aconv tm other)

  fun union_terms left right =
    List.rev (List.foldl (fn (tm, acc) =>
      if member tm acc then acc else tm :: acc) (List.rev left) right)

  fun subtract_terms left right =
    List.filter (fn tm => not (member tm right)) left

  fun genspec_available ty =
    ((ignore (Refute_Gen.spec_of ty); true)
     handle Refute_Gen.NoGenerator _ => false)

  fun guarded_gen variable continuation =
    case Refute_Gen.predicate_of (Term.type_of variable) of
      NONE => Gen (variable, continuation)
    | SOME predicate =>
        Gen (variable, Guard (Term.mk_comb (predicate, variable),
          continuation))

  fun gen_all variables continuation =
    List.foldr (fn (variable, plan) => guarded_gen variable plan)
      continuation variables

  fun fresh_variables avoids types =
    let
      val avoid_variables = List.concat (List.map Term.free_vars_lr avoids)
      fun fresh avoid ty =
        let val variable = Term.variant avoid (Term.mk_var ("x", ty))
        in (variable, variable :: avoid) end

      fun loop [] avoid variables = rev variables
        | loop (ty :: rest) avoid variables =
            let val (variable, avoid') = fresh avoid ty
            in loop rest avoid' (variable :: variables) end
    in
      loop types avoid_variables []
    end

  (*
     Plan compilation, ported from exhaustive_generators.ML:260--315.

     compile concl bound [] = gen_all (frees concl \\ bound) (Test concl)
     compile concl bound (a :: rest) =
       if optimise_equality andalso a is (l = r) then
         try_eq (l, r) orelse try_eq (r, l) orelse default
       else default

     try_eq (lhs, x), x a free not in frees(lhs) U bound:
       gen_all (frees a \\ {x})
         (Bind (x, lhs, fallback, compile concl (frees a U bound) rest))
     try_eq (lhs, C a1 ... an), C a fully-applied TypeBase constructor:
       gen_all (frees lhs \\ bound)
         (Split (lhs, [(C, [v1 ... vn],
           compile concl (frees lhs U {vs} U bound)
             ([v1 = a1, ... vn = an] @ rest))]))
     default:
       gen_all (frees a \\ bound)
         (Guard (a, compile concl (frees a U bound) rest))
  *)
  fun compile_plan (config : Refute_Core.config) goal =
    let
      val (assumptions, conclusion) = boolSyntax.strip_imp goal
      val smart_context =
        if #smart_generators (#qc config) then
          SOME (MFH.make_context (#mf config) [])
        else NONE
      type analysis =
        {result : SmartGen.inference_result option,
         trigger : bool, reason : string option}
      val analyses = ref ([] : (term * analysis) list)

      fun vars_of bound tm = subtract_terms (Term.free_vars_lr tm) bound

      fun premise_head premise =
        let val (head, _) = HolKernel.strip_comb premise
        in if Term.is_const head then SOME head else NONE end
        handle HOL_ERR _ => NONE

      fun error_text error =
        ((case General.exnMessage error of
              "" => "unexpected mode-inference exception"
            | text => text)
         handle Interrupt => raise Interrupt
              | _ => "unexpected mode-inference exception")

      fun safe_term_text tm =
        Parse.term_to_string tm
        handle Interrupt => raise Interrupt
             | _ => "<unprintable premise>"

      fun analyse relation =
        case List.find (fn (other, _) =>
               SmartGen.same_constant relation other) (!analyses) of
            SOME (_, answer) => answer
          | NONE =>
              let
                val answer =
                  case smart_context of
                      NONE => {result = NONE, trigger = false, reason = NONE}
                    | SOME context =>
                        (case MFH.instantiated_fixpoint_group context relation of
                             SOME {members, rules, ...} =>
                               (case SmartGen.infer_scc
                                  {members = members, rules = rules,
                                   triple_for = MFH.joint_intro_triple_for,
                                   external = [],
                                   reorder_premises =
                                     #reorder_premises (#qc config)} of
                                    SOME result =>
                                      {result = SOME result, trigger = true,
                                       reason = NONE}
                                  | NONE =>
                                      {result = NONE, trigger = true,
                                       reason = SOME
                                         "introduction-rule conversion failed"})
                           | NONE =>
                               (case SmartGen.horn_inference_clauses_for
                                   relation of
                                    SOME clauses =>
                                      {result = SOME (SmartGen.infer_group
                                        {members = [relation],
                                         clauses = clauses, external = [],
                                         reorder_premises =
                                           #reorder_premises (#qc config)}),
                                       trigger = true, reason = NONE}
                                  | NONE =>
                                      {result = NONE, trigger = false,
                                       reason = NONE}))
                val _ = analyses := (relation, answer) :: !analyses
                val _ = Option.app SmartGen.cache_inference (#result answer)
              in
                answer
              end
              handle Interrupt => raise Interrupt
                   | error =>
                       let
                         val answer =
                           {result = NONE, trigger = true,
                            reason = SOME (error_text error)}
                         val _ = analyses := (relation, answer) :: !analyses
                       in
                         answer
                       end

      fun smart_candidates bound assumption =
        case premise_head assumption of
            NONE => ([], false, NONE)
          | SOME relation =>
              let val {result, trigger, reason} = analyse relation
                  val inferred =
                    case result of
                        NONE => []
                      | SOME inference => SmartGen.goal_modes_for_call bound
                          assumption inference
                  val modes =
                    List.mapPartial (fn goal_mode as
                        ({mode, ...} : SmartGen.goal_mode) =>
                      Option.map (fn program => (goal_mode, program))
                        (SmartGen.enumerator_for relation mode)) inferred
                  val reason =
                    if not (null modes) orelse not trigger then reason
                    else if not (null inferred) then SOME
                      "CPS enumerator compilation failed for inferred mode"
                    else SOME (Option.getOpt (reason,
                      "no executable first-order positive mode"))
              in
                (modes, trigger, reason)
              end

      fun report_fallback assumption reason =
        Refute_Core.Private.say 2
          ("Refute smart generator fallback for " ^
           safe_term_text assumption ^ ": " ^ reason ^ "\n")

      datatype premise_action =
          Smart of SmartGen.goal_mode * SmartGen.enumerator
        | Ordinary

      fun orientation_score bound (lhs, rhs) =
        if Term.is_var rhs andalso
           not (member rhs (Term.free_vars_lr lhs)) andalso
           not (member rhs bound)
        then SOME
          {missing = length (vars_of bound lhs), functional = true,
           generator = false, outputs = 1, recursive = false}
        else
          case fully_applied_constructor rhs of
              NONE => NONE
            | SOME (_, arguments) => SOME
                {missing = length (vars_of bound lhs), functional = true,
                 generator = false, outputs = length arguments,
                 recursive = false}

      fun equality_score bound assumption =
        case Lib.total boolSyntax.dest_eq assumption of
            NONE => NONE
          | SOME (left, right) =>
              (case (orientation_score bound (left, right),
                     orientation_score bound (right, left)) of
                   (NONE, other) => other
                 | (other, NONE) => other
                 | (SOME first, SOME second) =>
                     if SmartGen.compare_score (second, first) = LESS
                     then SOME second else SOME first)

      fun ordinary_score bound assumption =
        if #optimise_equality (#qc config) then
          Option.getOpt (equality_score bound assumption,
            {missing = length (vars_of bound assumption),
             functional = false, generator = true, outputs = 0,
             recursive = false})
        else
          {missing = length (vars_of bound assumption),
           functional = false, generator = true, outputs = 0,
           recursive = false}

      fun action_for bound assumption =
        let
          val ordinary = (Ordinary, ordinary_score bound assumption)
          val (modes, trigger, reason) = smart_candidates bound assumption
          fun add ((mode as {score, ...} : SmartGen.goal_mode, program),
                   NONE) = SOME (Smart (mode, program), score)
            | add ((mode as {score, ...} : SmartGen.goal_mode, program),
                   current as SOME (_, old)) =
                if SmartGen.compare_score (score, old) = LESS then
                  SOME (Smart (mode, program), score)
                else current
          val smart = List.foldl add NONE modes
          val best =
            case smart of
                NONE => ordinary
              | SOME (candidate as (_, score)) =>
                  if SmartGen.compare_score (#2 ordinary, score) = LESS
                  then ordinary else candidate
        in
          (best, trigger, reason)
        end

      fun remove_nth selected entries =
        List.map #2 (List.filter (fn (index, _) => index <> selected)
          (Lib.enumerate 0 entries))

      fun select_premise bound entries =
        let
          fun candidate (index, assumption) =
            let val (scored, trigger, reason) = action_for bound assumption
            in (index, assumption, scored, trigger, reason) end
          val first = candidate (0, hd entries)
          val all =
            if #smart_generators (#qc config) andalso
               #reorder_premises (#qc config)
            then map candidate (Lib.enumerate 0 entries)
            else [first]
          val reorder = length all > 1 andalso
            List.exists (fn (_, _, _, trigger, _) => trigger) all
          val candidates = if reorder then all else [first]
          fun least (item as (_, _, (_, score), _, _)) NONE = SOME item
            | least (item as (_, _, (_, score), _, _))
                (current as SOME (_, _, (_, old), _, _)) =
                if SmartGen.compare_score (score, old) = LESS
                then SOME item else current
        in
          (valOf (List.foldl (fn (item, result) => least item result)
             NONE candidates), reorder)
        end

      fun compile conclusion bound assumptions =
        case assumptions of
          [] => gen_all (vars_of bound conclusion) (Test conclusion)
        | _ =>
            let
              val ((selected, assumption, (action, _), triggering, reason),
                   reorder) = select_premise bound assumptions
              val rest = remove_nth selected assumptions
              val assumption_vars = vars_of bound assumption
              val next_bound = union_terms assumption_vars bound
              fun continuation () = compile conclusion next_bound rest

              fun default () =
                gen_all assumption_vars (Guard (assumption, continuation ()))

              fun try_equality (lhs, rhs) =
                if Term.is_var rhs andalso
                   not (member rhs (Term.free_vars_lr lhs)) andalso
                   not (member rhs bound)
                then
                  let
                    val fallback =
                      if genspec_available (Term.type_of rhs) then
                        SOME (guarded_gen rhs (continuation ()))
                      else NONE
                    val variables = subtract_terms assumption_vars [rhs]
                  in
                    SOME (gen_all variables
                      (Bind (rhs, lhs, fallback, continuation ())))
                  end
                else
                  case fully_applied_constructor rhs of
                    NONE => NONE
                  | SOME (constructor, arguments) =>
                      let
                        val lhs_variables = vars_of bound lhs
                        val variables = fresh_variables
                          (conclusion :: assumptions @ bound)
                          (List.map Term.type_of arguments)
                        val equations = ListPair.mapEq boolSyntax.mk_eq
                          (variables, arguments)
                        val branch_bound = union_terms lhs_variables
                          (union_terms variables bound)
                        val branch = compile conclusion branch_bound
                          (equations @ rest)
                      in
                        SOME (gen_all lhs_variables
                          (Split (lhs, [(constructor, variables, branch)])))
                      end

              fun ordinary () =
                if #optimise_equality (#qc config) then
                  case Lib.total boolSyntax.dest_eq assumption of
                    NONE => default ()
                  | SOME (left, right) =>
                      let
                        val orientations =
                          if not reorder then
                            [(left, right), (right, left)]
                          else
                            (case (orientation_score bound (left, right),
                                   orientation_score bound (right, left)) of
                                 (SOME first, SOME second) =>
                                   if SmartGen.compare_score
                                        (second, first) = LESS
                                   then [(right, left), (left, right)]
                                   else [(left, right), (right, left)]
                               | _ => [(left, right), (right, left)])
                      in
                        case Lib.get_first try_equality orientations of
                            SOME result => result
                          | NONE => default ()
                      end
                else default ()
            in
              case action of
                  Smart ({mode, ins, outs, missing, ...},
                         {version, ...} : SmartGen.enumerator) =>
                    gen_all missing
                      (if null outs then
                         (Refute_Core.Private.say 2
                            ("Refute smart generator Guard for " ^
                             safe_term_text assumption ^ "\n");
                          SmartGuard
                            {predicate = assumption, version = version,
                             cont = continuation ()})
                       else
                         Enum {rel = valOf (premise_head assumption),
                               mode = mode, version = version,
                               ins = ins, outs = outs,
                               cont = continuation ()})
                | Ordinary =>
                    (if triggering then
                       report_fallback assumption
                         (Option.getOpt (reason,
                           "no executable first-order positive mode"))
                     else ();
                     ordinary ())
            end
    in
      if #smart_quantifier (#qc config) then
        compile conclusion [] assumptions
      else
        gen_all (Term.free_vars_lr goal) (Test goal)
    end

  fun pp_plan plan =
    let
      fun indent depth = String.implode (List.tabulate (depth, fn _ => #" "))
      fun show depth current =
        case current of
          Test tm => indent depth ^ "Test " ^ Parse.term_to_string tm
        | Gen (variable, continuation) =>
            indent depth ^ "Gen " ^ Parse.term_to_string variable ^ "\n" ^
            show (depth + 2) continuation
        | Bind (variable, expression, fallback, continuation) =>
            indent depth ^ "Bind " ^ Parse.term_to_string variable ^ " = " ^
            Parse.term_to_string expression ^
            (case fallback of NONE => "\n" | SOME plan =>
               "\n" ^ indent (depth + 2) ^ "fallback\n" ^
               show (depth + 4) plan ^ "\n") ^
            show (depth + 2) continuation
        | Split (scrutinee, branches) =>
            let
              fun branch (constructor, variables, continuation) =
                indent (depth + 2) ^ Parse.term_to_string constructor ^ " " ^
                String.concatWith " "
                  (List.map Parse.term_to_string variables) ^
                "\n" ^ show (depth + 4) continuation
            in
              indent depth ^ "Split " ^ Parse.term_to_string scrutinee ^ "\n" ^
              String.concatWith "\n" (List.map branch branches)
            end
        | Guard (predicate, continuation) =>
            indent depth ^ "Guard " ^ Parse.term_to_string predicate ^ "\n" ^
            show (depth + 2) continuation
        | SmartGuard {predicate, cont, ...} =>
            indent depth ^ "Smart Guard " ^
            Parse.term_to_string predicate ^ "\n" ^
            show (depth + 2) cont
        | Enum {rel, mode, ins, outs, cont, ...} =>
            indent depth ^ "Enum " ^ Parse.term_to_string rel ^ "[" ^
            SmartGen.mode_string mode ^ "] (" ^
            String.concatWith ", " (map Parse.term_to_string ins) ^
            ") -> (" ^
            String.concatWith ", " (map Parse.term_to_string outs) ^
            ")\n" ^ show (depth + 2) cont
        | Prune => indent depth ^ "Prune"
    in
      show 0 plan
    end

  fun schedule instances size =
    let
      val cards = List.map #card instances
      val size_matters = List.exists #size_matters instances
      fun compare ((card1, size1), (card2, size2)) =
        case Int.compare (card1 + size1, card2 + size2) of
            EQUAL => Int.compare (card1, card2)
          | order => order
    in
      if size_matters then
        Listsort.sort compare (List.concat (List.map (fn card =>
          List.tabulate (Int.max (0, size), fn index => (card, index + 1)))
          cards))
      else
        List.map (fn card => (card, size)) cards
    end

  fun elapsed_msec start =
    LargeInt.toInt (Time.toMilliseconds (Time.- (Time.now (), start)))
    handle _ => 0

  fun record_candidate
        {config : Refute_Core.config,
         backend : string,
         substrate : string,
         instance : Refute_Core.instance,
         stats : (string * int) list,
         counterexamples : Refute_Core.counterexample list ref,
         discarded : int ref,
         retry : bool -> candidate list -> unit}
        {env, genuine, genuine_only, ignored} =
    let
      val bindings = List.filter
        (fn (variable, _) =>
          List.exists (fn free => Term.aconv free variable)
            (Term.free_vars_lr (#goal instance)))
        env
      val cex : Refute_Core.counterexample =
        { backend = backend,
          substrate = substrate,
          certainty = if genuine then Refute_Core.Potential []
            else Refute_Core.Potential ["evaluation stuck during testing"],
          bindings = rev bindings,
          evals = [], cert = NONE, scope = NONE, model = NONE,
          stats = stats }
      val next = {env = env, genuine = genuine} :: ignored
    in
      (* QC hits retain their semantic Genuine grade when theorem replay is
         explicitly disabled; [cert = NONE] records the opt-out. *)
      if not (#certify (#qc config)) then
        counterexamples :=
          Refute_Cert.replace cex Refute_Core.Genuine [] NONE ::
          !counterexamples
      else
        case Refute_Cert.certify
          {original = #original instance, evals = #evals instance,
           env = env, cex = cex} of
            Refute_Cert.Certified certified =>
              counterexamples := certified :: !counterexamples
          | Refute_Cert.Discarded =>
              (discarded := !discarded + 1; retry genuine_only next)
          | Refute_Cert.Potential potential =>
              if #abort_potential config andalso not genuine_only then
                counterexamples := potential :: !counterexamples
              else if genuine_only then retry true next
              else
                (Refute_Core.report_outcome config
                   (Refute_Core.Counterexample [potential]);
                 retry true next)
    end

  fun plan_has_gen current =
    case current of
        Test _ => false
      | Gen _ => true
      | Bind (_, _, fallback, next) =>
          plan_has_gen next orelse
          (case fallback of
               NONE => false
             | SOME alternative => plan_has_gen alternative)
      | Split (_, branches) =>
          List.exists (fn (_, _, next) => plan_has_gen next) branches
      | Guard (_, next) => plan_has_gen next
      | SmartGuard {cont, ...} => plan_has_gen cont
      | Enum _ => true
      | Prune => false

  fun plan_uses_smart current =
    case current of
        Test _ => false
      | Gen (_, next) => plan_uses_smart next
      | Bind (_, _, fallback, next) =>
          plan_uses_smart next orelse
          (case fallback of
               NONE => false
             | SOME alternative => plan_uses_smart alternative)
      | Split (_, branches) =>
          List.exists (plan_uses_smart o #3) branches
      | Guard (_, next) => plan_uses_smart next
      | SmartGuard _ => true
      | Enum _ => true
      | Prune => false

  fun smart_gate_override_with preflight (config : Refute_Core.config)
        (backend : Refute_Core.backend) instances =
    let
      val native_capable =
        case #substrate (#qc config) of
            Refute_Core.Compute => false
          | Refute_Core.Cv => false
          | _ => true
      val plans = map (fn (instance : Refute_Core.instance) =>
        compile_plan config (#goal instance)) instances
      val gated_plans = List.mapPartial
        (fn (instance, plan) =>
          case #qc_gate instance of NONE => NONE | SOME _ => SOME plan)
        (ListPair.zip (instances, plans))
      val evals = List.concat
        (map (fn (instance : Refute_Core.instance) => #evals instance)
          instances)
    in
      #name backend = "exhaustive" andalso
      #smart_generators (#qc config) andalso native_capable andalso
      not (null gated_plans) andalso List.all plan_uses_smart gated_plans andalso
      null (preflight config Exhaustive plans evals)
    end
    handle Interrupt => raise Interrupt
         | _ => false

  fun smart_gate_override config backend instances =
    smart_gate_override_with Refute_Extract.native_preflight
      config backend instances

  fun substrate_name Refute_Core.Compute = SOME "compute"
    | substrate_name Refute_Core.Cv = SOME "cv"
    | substrate_name Refute_Core.NativeSML = SOME "native"
    | substrate_name Refute_Core.Auto = NONE

  fun add_reason reason reasons =
    if List.exists (fn old => old = reason) (!reasons) then ()
    else reasons := !reasons @ [reason]

  datatype selected_compile =
      Selected of string * compiled_test
    | SelectionFailed of string list

  fun say_selected name explicit =
    Refute_Core.Private.say 2
      ("Refute substrate selection: selected " ^ name ^
       (if explicit then " (explicit)" else "") ^ "\n")

  fun say_inapplicable name reasons =
    Refute_Core.Private.say 2
      ("Refute substrate selection: " ^ name ^
       " is inapplicable: " ^
       (if null reasons then "no reason supplied"
        else String.concatWith "; " reasons) ^ "\n")

  fun compile_auto config strategy problem =
    let
      fun try [] reasons =
            SelectionFailed
              (if null reasons then ["no substrate is registered"]
               else reasons)
        | try (substrate :: rest) reasons =
            (case #compile substrate config strategy problem of
                 Compiled test =>
                   (say_selected (#name substrate) false;
                    Selected (#name substrate, test))
               | Inapplicable why =>
                   (say_inapplicable (#name substrate) why;
                    try rest (reasons @ map (fn reason =>
                      #name substrate ^ ": " ^ reason) why)))
    in
      try (get_substrates ()) []
    end

  fun compile_explicit config choice strategy problem =
    let
      val name = valOf (substrate_name choice)
    in
      case List.find (fn substrate => #name substrate = name)
        (get_substrates ()) of
          NONE => SelectionFailed
            ["requested substrate " ^ name ^ " is unavailable"]
        | SOME substrate =>
            (case #compile substrate config strategy problem of
                 Compiled test =>
                   (say_selected name true; Selected (name, test))
               | Inapplicable reasons =>
                   (say_inapplicable name reasons;
                    SelectionFailed reasons))
    end

  fun compile_selected config strategy problem =
    case #substrate (#qc config) of
        Refute_Core.Auto => compile_auto config strategy problem
      | choice => compile_explicit config choice strategy problem

  fun bounded_size size = Int.max (0, size)

  fun strategy_seed (config : Refute_Core.config) =
    case #seed (#qc config) of
        SOME seed => normalize_seed (IntInf.fromInt seed)
      | NONE =>
          let
            val seed = !session_seed
            val _ = session_seed := rand_next seed
          in
            seed
          end

  fun is_random (Random _) = true
    | is_random Exhaustive = false
    | is_random Narrowing = false

  fun strategy_name Exhaustive = "exhaustive"
    | strategy_name (Random _) = "random"
    | strategy_name Narrowing = "narrowing"

  fun strategy_run strategy (config : Refute_Core.config)
      (instances : Refute_Core.instance list) =
    let
      (* Smart generators are the positive exhaustive CPS compilation.
         Random testing retains its existing generator/guard plans. *)
      val plan_config =
        case strategy of
            Random _ => Refute_Core.upd_smart_generators false config
          | _ => config
      val plans = List.map
        (fn instance => compile_plan plan_config (#goal instance)) instances
      val _ =
        if not (Refute_Core.Private.enabled 3) then ()
        else List.app (fn (instance, plan) =>
          Refute_Core.Private.say 3
            ("Refute plan (card " ^ Int.toString (#card instance) ^
             "):\n" ^ pp_plan plan ^ "\n"))
          (ListPair.zip (instances, plans))
      val paired = ListPair.zip (instances, plans)
      val gated = List.exists (Option.isSome o #qc_gate) instances
      val original_gate_reasons = List.concat
        (List.mapPartial (fn (instance : Refute_Core.instance) =>
          #qc_gate instance) instances)
      val native_capable =
        case #substrate (#qc config) of
            Refute_Core.Compute => false
          | Refute_Core.Cv => false
          | _ => true
      val every_gated_plan_is_smart = List.all (fn (instance, plan) =>
        not (Option.isSome (#qc_gate instance)) orelse plan_uses_smart plan)
        paired
      val can_preflight = gated andalso strategy = Exhaustive andalso
        #smart_generators (#qc config) andalso native_capable andalso
        every_gated_plan_is_smart
      val preflight_reasons =
        if can_preflight then
          Refute_Extract.native_preflight config strategy plans
            (List.concat (map (fn (instance : Refute_Core.instance) =>
              #evals instance) instances))
        else []
      val gate_reasons =
        if not gated then []
        else if can_preflight andalso null preflight_reasons then []
        else original_gate_reasons @ preflight_reasons @
          (if native_capable orelse is_random strategy then []
           else ["smart generators require an Enum-capable native substrate"])
    in
      if not (null gate_reasons) then Refute_Core.Unknown gate_reasons
      else case compile_selected config strategy (Plans plans) of
          SelectionFailed reasons => Refute_Core.Unknown reasons
        | Selected (substrate, compiled) =>
            if gated andalso substrate <> "native" then
              (#close compiled ();
               Refute_Core.Unknown
                 ["smart-gated plans require the native substrate"])
            else let
              fun selected_body () =
                let
                  val entries = schedule instances (#size (#qc config))
              val complete = ref
                (case strategy of
                     Exhaustive => not (null entries)
                   | Random _ => List.all (not o plan_has_gen) plans
                   | Narrowing => false)
              val counterexamples = ref []
              val discarded = ref 0
              val gave_up = ref []
              fun instance_for card = List.nth (instances, card - 1)
              fun stats_for size card msec =
                !(#last_stats compiled) @
                (if !discarded = 0 then []
                 else [("discarded", !discarded)]) @
                [("size", size), ("card", card), ("msec", msec)]
              fun one (card, size) draws genuine_only ignored =
                let
                  val start = Time.now ()
                  val result = #run compiled
                    { genuine_only = genuine_only,
                      card = card,
                      size = size,
                      draws = draws,
                      ignored = ignored }
                  val msec = elapsed_msec start
                in
                  case result of
                      Exhausted {complete = entry_complete} =>
                        complete := (!complete andalso entry_complete)
                    | GaveUp reason =>
                        (complete := false; add_reason reason gave_up)
                    | CexFound {env, genuine} =>
                        record_candidate
                          { config = config,
                            backend = strategy_name strategy,
                            substrate = substrate,
                            instance = instance_for card,
                            stats = stats_for size card msec,
                            counterexamples = counterexamples,
                            discarded = discarded,
                            retry = fn go => fn ig =>
                              one (card, size) draws go ig }
                          { env = env,
                            genuine = genuine,
                            genuine_only = genuine_only,
                            ignored = ignored }
                end
              fun run_entry entry =
                let
                  val started = Time.now ()
                  val total = bounded_size (#iterations (#qc config))
                  val target = Int.max (1, #max_counterexamples config)
                  fun chunks 0 = ()
                    | chunks remaining =
                        if length (!counterexamples) >= target then ()
                        else
                          let
                            val draws =
                              if target > 1 then 1
                              else
                                case #max_chunk compiled of
                                    NONE => remaining
                                  | SOME chunk =>
                                      Int.min (chunk, remaining)
                            val reasons_before = length (!gave_up)
                            val _ = one entry draws
                              (#genuine_only config) []
                          in
                            if length (!gave_up) > reasons_before then ()
                            else chunks (remaining - draws)
                          end
                  val _ =
                    if is_random strategy then
                      if total = 0 then ()
                      else chunks total
                    else one entry 0 (#genuine_only config) []
                  val (card, size) = entry
                  val backend = strategy_name strategy
                  val elapsed = elapsed_msec started
                  val _ = Refute_Core.Private.say 2
                    ("Refute schedule entry (backend: " ^ backend ^
                     ", substrate: " ^ substrate ^ ", card " ^
                     Int.toString card ^ ", size " ^ Int.toString size ^
                     "): " ^ Int.toString elapsed ^ "ms\n")
                in
                  ()
                end
              fun search [] = ()
                | search (entry :: rest) =
                    if length (!counterexamples) >=
                      Int.max (1, #max_counterexamples config)
                    then ()
                    else (run_entry entry; search rest)
              val _ = search entries
              val generic_reason =
                case strategy of
                    Random _ => "random search exhausted"
                  | Exhaustive => "search space not exhausted"
                  | Narrowing => "narrowing search exhausted"
            in
                  if not (null (!counterexamples)) then
                    Refute_Core.Counterexample (rev (!counterexamples))
                  else if !complete then Refute_Core.NoCounterexample
                  else Refute_Core.Unknown (generic_reason :: !gave_up)
                end
              val body_result = Exn.capture selected_body ()
              val close_result = Exn.capture (#close compiled) ()
            in
              case close_result of
                  Exn.Res _ => Exn.release body_result
                | Exn.Exn error => raise error
            end
    end

  val exhaustive_backend : Refute_Core.backend =
    { name = "exhaustive",
      weight = 20,
      configured = fn () => true,
      requires = Refute_Core.ExecutableGoal,
      input = Refute_Core.MonoInstances,
      run = strategy_run Exhaustive }

  val random_backend : Refute_Core.backend =
    { name = "random",
      weight = 30,
      configured = fn () => true,
      requires = Refute_Core.ExecutableGoal,
      input = Refute_Core.MonoInstances,
      run = fn config =>
        strategy_run (Random {seed = strategy_seed config}) config }

  fun register_backends () =
    (Refute_Core.executable_goal_override := smart_gate_override;
     Refute_EvalSML.register_substrate ();
     Refute_EvalCompute.register_substrate ();
     Refute_EvalCv.register_substrate ();
     Refute_Core.register_backend exhaustive_backend;
     Refute_Core.register_backend random_backend)

  val _ = register_backends ()
end
