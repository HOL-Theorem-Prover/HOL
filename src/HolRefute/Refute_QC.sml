structure Refute_QC = struct
  type term = Term.term
  open Refute_Cert Refute_Eval

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

  fun fully_applied_constructor tm =
    let
      val (constructor, arguments) = boolSyntax.strip_comb tm
      val (domain, _) = boolSyntax.strip_fun (Term.type_of constructor)
    in
      if TypeBase.is_constructor constructor andalso
         length domain = length arguments
      then SOME (constructor, arguments)
      else NONE
    end

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

      fun vars_of bound tm = subtract_terms (Term.free_vars_lr tm) bound

      fun compile conclusion bound assumptions =
        case assumptions of
          [] => gen_all (vars_of bound conclusion) (Test conclusion)
        | assumption :: rest =>
            let
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
                      else
                        NONE
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
            in
              if #optimise_equality (#qc config) then
                case Lib.total boolSyntax.dest_eq assumption of
                  NONE => default ()
                | SOME (left, right) =>
                    (case try_equality (left, right) of
                       SOME result => result
                     | NONE =>
                         (case try_equality (right, left) of
                            SOME result => result
                          | NONE => default ()))
              else
                default ()
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
          evals = [], cert = NONE, scope = NONE,
          stats = stats }
      val next = {env = env, genuine = genuine} :: ignored
    in
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
      | Prune => false

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

  fun compile_auto config strategy plans =
    let
      fun try [] reasons =
            SelectionFailed
              (if null reasons then ["no substrate is registered"]
               else reasons)
        | try (substrate :: rest) reasons =
            (case #compile substrate config strategy plans of
                 Compiled test =>
                   (Refute_Core.Private.say 2
                      ("Refute substrate selection: selected " ^
                       #name substrate ^ "\n");
                    Selected (#name substrate, test))
               | Inapplicable why =>
                   let
                     val detail =
                       if null why then "no reason supplied"
                       else String.concatWith "; " why
                     val _ = Refute_Core.Private.say 2
                       ("Refute substrate selection: " ^ #name substrate ^
                        " is inapplicable: " ^ detail ^ "\n")
                   in
                     try rest (reasons @ map (fn reason =>
                       #name substrate ^ ": " ^ reason) why)
                   end)
    in
      try (get_substrates ()) []
    end

  fun compile_explicit config choice strategy plans =
    let
      val name = valOf (substrate_name choice)
    in
      case List.find (fn substrate => #name substrate = name)
        (get_substrates ()) of
          NONE => SelectionFailed
            ["requested substrate " ^ name ^ " is unavailable"]
        | SOME substrate =>
            (case #compile substrate config strategy plans of
                 Compiled test =>
                   (Refute_Core.Private.say 2
                      ("Refute substrate selection: selected " ^ name ^
                       " (explicit)\n");
                    Selected (name, test))
               | Inapplicable reasons =>
                   (Refute_Core.Private.say 2
                      ("Refute substrate selection: " ^ name ^
                       " is inapplicable: " ^
                       (if null reasons then "no reason supplied"
                        else String.concatWith "; " reasons) ^ "\n");
                    SelectionFailed reasons))
    end

  fun compile_selected config strategy plans =
    case #substrate (#qc config) of
        Refute_Core.Auto => compile_auto config strategy plans
      | choice => compile_explicit config choice strategy plans

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

  fun strategy_run strategy (config : Refute_Core.config)
      (instances : Refute_Core.instance list) =
    let
      val plans = List.map
        (fn instance => compile_plan config (#goal instance)) instances
      val _ =
        if not (Refute_Core.Private.enabled 3) then ()
        else List.app (fn (instance, plan) =>
          Refute_Core.Private.say 3
            ("Refute plan (card " ^ Int.toString (#card instance) ^
             "):\n" ^ pp_plan plan ^ "\n"))
          (ListPair.zip (instances, plans))
    in
      case compile_selected config strategy plans of
          SelectionFailed reasons => Refute_Core.Unknown reasons
        | Selected (substrate, compiled) =>
            let
              fun selected_body () =
                let
                  val entries = schedule instances (#size (#qc config))
              val complete = ref
                (case strategy of
                     Exhaustive => not (null entries)
                   | Random _ => List.all (not o plan_has_gen) plans)
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
                            backend = if is_random strategy then "random"
                              else "exhaustive",
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
                              else if substrate = "cv" then
                                Int.min (1024, remaining)
                              else remaining
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
                  val backend =
                    if is_random strategy then "random" else "exhaustive"
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
                if is_random strategy then "random search exhausted"
                else "search space not exhausted"
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
      run = strategy_run Exhaustive }

  val random_backend : Refute_Core.backend =
    { name = "random",
      weight = 30,
      configured = fn () => true,
      run = fn config =>
        strategy_run (Random {seed = strategy_seed config}) config }

  fun register_backends () =
    (Refute_EvalSML.register_substrate ();
     Refute_EvalCompute.register_substrate ();
     Refute_EvalCv.register_substrate ();
     Refute_Core.register_backend exhaustive_backend;
     Refute_Core.register_backend random_backend)

  val _ = register_backends ()
end
