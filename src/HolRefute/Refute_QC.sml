structure Refute_QC = struct
  type term = Term.term
  open Refute_Cert

  datatype plan =
      Test of term
    | Gen of term * plan
    | Bind of term * term * plan option * plan
    | Split of term * (term * term list * plan) list
    | Guard of term * plan
    | Prune

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

  type candidate = {env : (term * term) list, genuine : bool}

  datatype verdict = Continue | Found of candidate

  datatype run_result =
      CexFound of candidate
    | Exhausted of {complete : bool}
    | GaveUp of string

  type compiled_test =
    { run : {genuine_only : bool,
             card : int,
             size : int,
             ignored : candidate list} -> run_result,
      last_stats : (string * int) list ref }

  type substrate =
    { name : string,
      compile : Refute_Core.config -> plan list -> compiled_test }

  fun same_env [] [] = true
    | same_env ((variable1, value1) :: rest1)
        ((variable2, value2) :: rest2) =
        Term.aconv variable1 variable2 andalso
        Term.aconv value1 value2 andalso same_env rest1 rest2
    | same_env _ _ = false

  fun ignored_candidate env ignored =
    List.exists (fn candidate => same_env env (#env candidate)) ignored

  fun eval_rhs env tm =
    SOME (rhs_of (eval (instantiate env tm)))
    handle Interrupt => raise Interrupt | _ => NONE

  datatype boolean_value = IsTrue | IsFalse | IsStuck

  fun eval_boolean env tm =
    case eval_rhs env tm of
        SOME value =>
          if Term.aconv value boolSyntax.T then IsTrue
          else if Term.aconv value boolSyntax.F then IsFalse
          else IsStuck
      | NONE => IsStuck

  fun numeric_terms Refute_Gen.Num size =
        List.tabulate (Int.max (0, size) + 1, numSyntax.term_of_int)
    | numeric_terms Refute_Gen.Int size =
        List.tabulate (2 * Int.max (0, size) + 1,
          fn index => intSyntax.term_of_int
            (Arbint.fromInt (index - Int.max (0, size))))
    | numeric_terms Refute_Gen.Char _ =
        List.tabulate (Refute_Gen.enum_cap,
          fn index => stringSyntax.mk_chr (numSyntax.term_of_int index))
    | numeric_terms (Refute_Gen.Word width) size =
        List.tabulate (Int.min (Int.max (0, size),
          Int.max (0, Refute_Gen.int_power 2 width - 1)) + 1,
          fn index => wordsSyntax.mk_wordii (index, width))

  fun enum_args [] _ continuation = continuation []
    | enum_args (spec :: rest) size continuation =
        exhaustive_values spec size (fn value =>
          case enum_args rest size
            (fn values => continuation (value :: values)) of
              Continue => Continue
            | found => found)

  and exhaustive_function dom rng size continuation =
    case Refute_Gen.enumerate (Type.mk_type ("fun", [dom, rng])) of
        SOME graphs =>
          List.foldl (fn (graph, result) =>
            case result of Continue => continuation graph | found => found)
            Continue graphs
      | NONE =>
          let
            val variable = Term.mk_var ("x", dom)
            fun constants () =
              exhaustive_values (Refute_Gen.spec_of rng) size (fn value =>
                continuation (Term.mk_abs (variable, value)))
            fun layers 0 = Continue
              | layers remaining =
                  exhaustive_values (Refute_Gen.spec_of dom) size (fn point =>
                    exhaustive_values (Refute_Gen.spec_of rng) size
                      (fn value =>
                      let
                        fun one base = continuation
                          (Term.mk_comb
                            (combinSyntax.mk_update (point, value), base))
                      in
                        case exhaustive_function dom rng (remaining - 1) one of
                            Continue => Continue
                          | found => found
                      end))
          in
            case constants () of Continue => layers size | found => found
          end

  and exhaustive_values spec size continuation =
    case spec of
        Refute_Gen.GenEnum values =>
          List.foldl (fn (value, result) =>
            case result of Continue => continuation value | found => found)
            Continue values
      | Refute_Gen.GenNum kind =>
          List.foldl (fn (value, result) =>
            case result of Continue => continuation value | found => found)
            Continue (numeric_terms kind size)
      | Refute_Gen.GenCustom {enumerate = SOME enum, ...} =>
          List.foldl (fn (value, result) =>
            case result of Continue => continuation value | found => found)
            Continue (enum size)
      | Refute_Gen.GenCustom _ => Continue
      | Refute_Gen.GenDatatype {constrs, ...} =>
          if size <= 0 then Continue
          else
            List.foldl (fn ((constructor, args), result) =>
              case result of
                  Found _ => result
                | Continue =>
                    enum_args (List.map Refute_Gen.spec_of args) (size - 1)
                      (fn values => continuation
                        (Term.list_mk_comb (constructor, values))))
              Continue constrs
      | Refute_Gen.GenFun (dom, rng) =>
          exhaustive_function dom rng size continuation

  (* Shared plan traversal for both backends.  Every plan node is handled
     identically; the two backends differ only in how they instantiate a
     Gen binder, which is supplied as the [gen] callback.  Returns the
     search verdict together with the stats gathered for this run. *)
  fun traverse gen genuine_only ignored plan =
    let
      val complete = ref true
      val match_failures = ref 0
      val tests = ref 0

      fun candidate env genuine =
        if ignored_candidate env ignored then Continue
        else Found {env = env, genuine = genuine}

      fun visit env genuine current =
        case current of
            Prune => Continue
          | Test tm =>
              (tests := !tests + 1;
               case eval_boolean env tm of
                   IsTrue => Continue
                 | IsFalse =>
                     if genuine orelse not genuine_only then
                       candidate env genuine
                     else Continue
                 | IsStuck =>
                     (complete := false;
                      if genuine_only then Continue
                      else candidate env false))
          | Guard (tm, next) =>
              (case eval_boolean env tm of
                   IsTrue => visit env genuine next
                 | IsFalse => Continue
                 | IsStuck =>
                     (complete := false;
                      if genuine_only then Continue
                      else visit env false next))
          | Bind (variable, tm, fallback, next) =>
              (case eval_rhs env tm of
                   SOME value =>
                     visit ((variable, value) :: env) genuine next
                 | NONE =>
                     (complete := false;
                      case fallback of
                          NONE => Continue
                        | SOME alternative =>
                            if genuine_only then Continue
                            else visit env false alternative))
          | Split (tm, branches) =>
              (case eval_rhs env tm of
                   SOME value =>
                     (case fully_applied_constructor value of
                          NONE =>
                            (complete := false;
                             match_failures := !match_failures + 1;
                             Continue)
                        | SOME (constructor, args) =>
                            (case List.find (fn (expected, variables, _) =>
                              Term.same_const expected constructor andalso
                              length variables = length args) branches of
                                 NONE =>
                                   (complete := false;
                                    match_failures := !match_failures + 1;
                                    Continue)
                               | SOME (_, variables, next) =>
                                   visit
                                     (ListPair.zip (variables, args) @ env)
                                     genuine next))
                 | NONE =>
                     (complete := false;
                      match_failures := !match_failures + 1;
                      Continue))
          | Gen (variable, next) =>
              gen visit complete env genuine variable next
      val result = visit [] true plan
    in
      { result = result,
        complete = !complete,
        stats = [("tests", !tests),
          ("match_failures", !match_failures)] }
    end

  fun compute_compile (config : Refute_Core.config) plans =
    let
      val last_stats = ref []
      fun run {genuine_only, card, size, ignored} =
        let
          val plan = List.nth (plans, card - 1)
          fun gen visit complete env genuine variable next =
            let
              val ty = Term.type_of variable
              fun try value =
                visit ((variable, value) :: env) genuine next
            in
              case Refute_Gen.enumerate ty of
                  SOME values =>
                    List.foldl (fn (value, result) =>
                      case result of
                          Continue => try value
                        | found => found)
                      Continue values
                | NONE =>
                    (complete := false;
                     exhaustive_values (Refute_Gen.spec_of ty) size try)
            end
          val {result, complete, stats} =
            traverse gen genuine_only ignored plan
          val _ = last_stats := stats
        in
          case result of
              Found candidate => CexFound candidate
            | Continue => Exhausted {complete = complete}
        end
    in
      {run = run, last_stats = last_stats}
    end

  val compute_substrate : substrate =
    { name = "compute",
      compile = compute_compile }

  val substrates : substrate list ref = ref [compute_substrate]

  fun selected_substrate Refute_Core.Auto = SOME compute_substrate
    | selected_substrate Refute_Core.Compute = SOME compute_substrate
    | selected_substrate _ = NONE

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

  (* Shared certify + retry policy for both QC backends.  Given a witness
     the compiled search reported, build the counterexample record, run it
     through Refute_Cert.certify, and apply the Certified/Discarded/
     Potential policy.  `retry go ig` re-runs the backend's own search with
     the extended ignore-set (each backend passes its own continuation). *)
  fun record_candidate
        {config : Refute_Core.config,
         backend : string,
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

  val session_rng = ref (Random.newgenseed 42.0)

  fun bounded_size size = Int.max (0, size)

  fun random_number Refute_Gen.Num size rng =
        numSyntax.term_of_int (Random.range (0, bounded_size size + 1) rng)
    | random_number Refute_Gen.Int size rng =
        intSyntax.term_of_int (Arbint.fromInt
          (Random.range (~(bounded_size size), bounded_size size + 1) rng))
    | random_number Refute_Gen.Char _ rng =
        stringSyntax.mk_chr (numSyntax.term_of_int (Random.range (0, 256) rng))
    | random_number (Refute_Gen.Word width) _ rng =
        wordsSyntax.mk_wordii (Random.range
          (0, Refute_Gen.int_power 2 width) rng, width)

  fun random_entry spec size rng =
    let
      val floor = Refute_Gen.own_floor spec
    in
      random_value spec {budget = Int.max (floor, bounded_size size),
        size = bounded_size size} rng
    end

  and random_args [] [] _ _ rng = ([], rng)
    | random_args (ty :: tys) (is_recursive :: recursive) budget size rng =
        let
          val (value, rng') =
            if is_recursive then
              random_value (Refute_Gen.spec_of ty)
                {budget = Int.max (0, budget - 1), size = size} rng
            else
              random_entry (Refute_Gen.spec_of ty) size rng
          val (values, rng'') = random_args tys recursive budget size rng'
        in
          (value :: values, rng'')
        end
    | random_args _ _ _ _ _ =
        raise Fail "Refute_QC.random_args: malformed datatype generator"

  and random_function dom rng_ty size rng =
    let
      val variable = Term.mk_var ("x", dom)
      val (default, rng') = random_entry (Refute_Gen.spec_of rng_ty) size rng
      fun draw_points 0 current_rng = ([], current_rng)
        | draw_points count current_rng =
            let
              val (point, next_rng) =
                random_entry (Refute_Gen.spec_of dom) size current_rng
              val (points, final_rng) = draw_points (count - 1) next_rng
            in
              (point :: points, final_rng)
            end
      val (points, rng'') =
        case Refute_Gen.enumerate dom of
            SOME values => (values, rng')
          | NONE => draw_points (bounded_size size) rng'
      fun add (point, (base, current_rng)) =
        let
          val (value, next_rng) =
            random_entry (Refute_Gen.spec_of rng_ty) size current_rng
        in
          (Term.mk_comb (combinSyntax.mk_update (point, value), base),
           next_rng)
        end
      val (result, rng''') = List.foldl add
        (Term.mk_abs (variable, default), rng'') points
    in
      (result, rng''')
    end

  and random_value spec {budget, size} rng =
    case spec of
        Refute_Gen.GenEnum values =>
          if null values then
            raise Fail "Refute_QC.random_value: empty enumeration"
          else (List.nth (values, Random.range (0, length values) rng), rng)
      | Refute_Gen.GenNum kind => (random_number kind size rng, rng)
      | Refute_Gen.GenCustom {random = SOME generate, ...} =>
          (generate size rng, rng)
      | Refute_Gen.GenCustom _ =>
          raise Fail "Refute_QC.random_value: no random generator"
      | Refute_Gen.GenFun (dom, rng_ty) => random_function dom rng_ty size rng
      | Refute_Gen.GenDatatype {constrs, recursive, min_size, ...} =>
          let
            fun weight (flags, floors) =
              if not (List.exists (fn flag => flag) flags) then 1
              else
                let
                  fun depth (true, floor) = Int.max (0, floor - 1)
                    | depth (false, _) = 0
                  val minimum = List.foldl Int.max 0
                    (ListPair.mapEq depth (flags, floors))
                in
                  if minimum = 0 then budget
                  else if budget > minimum then budget else 0
                end
            fun entries [] [] [] = []
              | entries (constr :: rest) (flags :: more_flags)
                  (floors :: more_floors) =
                  let val entry = (constr, flags, weight (flags, floors))
                  in entry :: entries rest more_flags more_floors end
              | entries _ _ _ =
                  raise Fail "Refute_QC.random_value: malformed datatype"
            val choices = entries constrs recursive min_size
            val total = List.foldl (fn ((_, _, value), sum) => sum + value)
              0 choices
            val choice = Random.range (0, total) rng
            fun select _ [] =
                  raise Fail "Refute_QC.random_value: no constructor"
              | select remaining ((constructor, flags, weight) :: rest) =
                  if remaining < weight then (constructor, flags)
                  else select (remaining - weight) rest
            val ((constructor, arg_types), flags) = select choice choices
            val (arguments, rng') =
              random_args arg_types flags budget size rng
          in
            (Term.list_mk_comb (constructor, arguments), rng')
          end

  fun random_term ty size rng = random_entry (Refute_Gen.spec_of ty) size rng

  fun plan_has_gen current =
    case current of
        Test _ => false
      | Gen _ => true
      | Bind (_, _, fallback, next) =>
          plan_has_gen next orelse
          (case fallback of NONE => false | SOME alternative =>
             plan_has_gen alternative)
      | Split (_, branches) =>
          List.exists (fn (_, _, next) => plan_has_gen next) branches
      | Guard (_, next) => plan_has_gen next
      | Prune => false

  fun exhaustive_run (config : Refute_Core.config)
      (instances : Refute_Core.instance list) =
          let
            val plans = List.map
              (fn instance => compile_plan config (#goal instance))
              instances
          in
            case selected_substrate (#substrate (#qc config)) of
                NONE =>
                  Refute_Core.Unknown ["requested substrate is unavailable"]
              | SOME substrate =>
                    let
                      val compiled = #compile substrate config plans
                      val entries = schedule instances (#size (#qc config))
                      val complete = ref (not (null entries))
                      val counterexamples = ref []
                      val discarded = ref 0
                      fun instance_for card =
                        List.nth (instances, card - 1)
                      fun stats_for size card msec =
                        !(#last_stats compiled) @
                        (if !discarded = 0 then []
                         else [("discarded", !discarded)]) @
                        [("size", size), ("card", card), ("msec", msec)]
                      fun one (card, size) genuine_only ignored =
                        let
                          val start = Time.now ()
                          val result = #run compiled
                            {genuine_only = genuine_only,
                             card = card, size = size, ignored = ignored}
                          val msec = elapsed_msec start
                        in
                          case result of
                              Exhausted {complete = entry_complete} =>
                                complete := (!complete andalso entry_complete)
                            | GaveUp reason => complete := false
                            | CexFound {env, genuine} =>
                                record_candidate
                                  {config = config,
                                   backend = "exhaustive",
                                   instance = instance_for card,
                                   stats = stats_for size card msec,
                                   counterexamples = counterexamples,
                                   discarded = discarded,
                                   retry = fn go => fn ig =>
                                     one (card, size) go ig}
                                  {env = env, genuine = genuine,
                                   genuine_only = genuine_only,
                                   ignored = ignored}
                        end
                      fun search [] = ()
                        | search (entry :: rest) =
                            if length (!counterexamples) >=
                              Int.max (1, #max_counterexamples config)
                            then ()
                            else (one entry (#genuine_only config) [];
                                  search rest)
                      val _ = search entries
                    in
                      if not (null (!counterexamples)) then
                        Refute_Core.Counterexample (rev (!counterexamples))
                      else if !complete then Refute_Core.NoCounterexample
                      else Refute_Core.Unknown ["search space not exhausted"]
                    end
          end

  val exhaustive_backend : Refute_Core.backend =
    { name = "exhaustive", weight = 20, configured = fn () => true,
      run = exhaustive_run }

  fun random_compile plans rng =
    let
      val last_stats = ref []
      fun run {genuine_only, card, size, ignored} =
        let
          val plan = List.nth (plans, card - 1)
          fun gen visit _ env genuine variable next =
            let
              val (value, _) =
                random_term (Term.type_of variable) size rng
            in
              visit ((variable, value) :: env) genuine next
            end
          val {result, complete, stats} =
            traverse gen genuine_only ignored plan
          val _ = last_stats := stats
        in
          case result of
              Found candidate => CexFound candidate
            | Continue => Exhausted {complete = complete}
        end
        handle Refute_Gen.NoGenerator (_, reason) => GaveUp reason
             | Fail reason => GaveUp reason
    in
      {run = run, last_stats = last_stats}
    end

  fun random_run (config : Refute_Core.config)
      (instances : Refute_Core.instance list) =
          let
            val plans = List.map
              (fn instance => compile_plan config (#goal instance))
              instances
            val rng =
              case #seed (#qc config) of
                  SOME seed => Random.newgenseed (Real.fromInt seed)
                | NONE => !session_rng
            val compiled = random_compile plans rng
            val entries = schedule instances (#size (#qc config))
            val complete = ref (List.all (fn plan => not (plan_has_gen plan))
              plans)
            val counterexamples = ref []
            val discarded = ref 0
            fun instance_for card = List.nth (instances, card - 1)
            fun stats_for size card =
              !(#last_stats compiled) @
              (if !discarded = 0 then [] else [("discarded", !discarded)]) @
              [("size", size), ("card", card)]
            fun draw card size genuine_only ignored =
              case #run compiled
                { genuine_only = genuine_only,
                  card = card, size = size, ignored = ignored } of
                  Exhausted {complete = entry_complete} =>
                    complete := (!complete andalso entry_complete)
                | GaveUp _ => complete := false
                | CexFound {env, genuine} =>
                    record_candidate
                      {config = config, backend = "random",
                       instance = instance_for card,
                       stats = stats_for size card,
                       counterexamples = counterexamples,
                       discarded = discarded,
                       retry = fn go => fn ig => draw card size go ig}
                      {env = env, genuine = genuine,
                       genuine_only = genuine_only, ignored = ignored}
            fun draws 0 _ _ = ()
              | draws remaining card size =
                  if length (!counterexamples) >=
                    Int.max (1, #max_counterexamples config)
                  then ()
                  else (draw card size (#genuine_only config) [];
                        draws (remaining - 1) card size)
            fun search [] = ()
              | search ((card, size) :: rest) =
                  if length (!counterexamples) >=
                    Int.max (1, #max_counterexamples config)
                  then ()
                  else (draws (bounded_size (#iterations (#qc config)))
                    card size; search rest)
            val _ = search entries
          in
            if not (null (!counterexamples)) then
              Refute_Core.Counterexample (rev (!counterexamples))
            else if !complete then Refute_Core.NoCounterexample
            else Refute_Core.Unknown ["random search exhausted"]
          end

  val random_backend : Refute_Core.backend =
    { name = "random", weight = 30, configured = fn () => true,
      run = random_run }

  (* Register the built-in backends.  register_backend de-duplicates by
     name, so calling this more than once is idempotent.  Refute.sml calls
     it as well, so the backends are registered through the public entry
     point and not only when Refute_QC is opened directly (e.g. in
     selftest). *)
  fun register_backends () =
    (Refute_Core.register_backend exhaustive_backend;
     Refute_Core.register_backend random_backend)

  val _ = register_backends ()
end
