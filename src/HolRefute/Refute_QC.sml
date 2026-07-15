structure Refute_QC = struct
  type term = Term.term

  datatype plan =
      Test of term
    | Gen of term * plan
    | Bind of term * term * plan option * plan
    | Split of term * (term * term list * plan) list
    | Guard of term * plan
    | Prune

  fun member tm = List.exists (fn other => Term.aconv tm other)

  fun union_terms left right =
    List.foldl (fn (tm, acc) =>
      if member tm acc then acc else acc @ [tm]) left right

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
        in (variable, avoid @ [variable]) end

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

  datatype verdict = Continue | Found of
    {env : (term * term) list, genuine : bool}

  datatype run_result =
      CexFound of {env : (term * term) list, genuine : bool}
    | Exhausted of {complete : bool}
    | GaveUp of string

  type compiled_test =
    { run : {genuine_only : bool, card : int, size : int} -> run_result }

  type substrate =
    { name : string,
      applicable : Refute_Core.problem * plan list -> bool,
      compile : Refute_Core.config -> plan list -> compiled_test }

  val last_stats : (string * int) list ref = ref []

  fun eval_rhs env tm =
    let
      val theorem = computeLib.CBV_CONV (!computeLib.the_compset)
        (Term.subst (List.map (fn (redex, residue) =>
          {redex = redex, residue = residue}) env) tm)
    in
      SOME (#2 (boolSyntax.dest_eq (Thm.concl theorem)))
    end
    handle _ => NONE

  datatype boolean_value = IsTrue | IsFalse | IsStuck

  fun eval_boolean env tm =
    case eval_rhs env tm of
        SOME value =>
          if Term.aconv value boolSyntax.T then IsTrue
          else if Term.aconv value boolSyntax.F then IsFalse
          else IsStuck
      | NONE => IsStuck

  fun constructor_value tm =
    case fully_applied_constructor tm of
        SOME result => SOME result
      | NONE => NONE

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
          Refute_Gen.int_power 2 width) + 1,
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

  fun compute_compile (config : Refute_Core.config) plans =
    let
      fun run {genuine_only, card, size} =
        let
          val complete = ref true
          val match_failures = ref 0
          val tests = ref 0
          val plan = List.nth (plans, card - 1)

          fun visit env genuine current =
            case current of
                Prune => Continue
              | Test tm =>
                  (tests := !tests + 1;
                   case eval_boolean env tm of
                       IsTrue => Continue
                     | IsFalse =>
                         if genuine orelse not genuine_only then
                           Found {env = env, genuine = genuine}
                         else Continue
                     | IsStuck =>
                         (complete := false;
                          if genuine_only then Continue
                          else Found {env = env, genuine = false}))
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
                         (case constructor_value value of
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
                  let
                    val ty = Term.type_of variable
                    val spec = Refute_Gen.spec_of ty
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
                           exhaustive_values spec size try)
                  end
          val result = visit [] true plan
          val _ = last_stats := [("tests", !tests),
            ("match_failures", !match_failures)]
        in
          case result of
              Found candidate => CexFound candidate
            | Continue => Exhausted {complete = !complete}
        end
    in
      {run = run}
    end

  fun compute_applicable (problem, _) =
    null (Refute_Core.nonexecutable_constants
      (#goal problem :: #evals problem))

  val compute_substrate : substrate =
    { name = "compute",
      applicable = compute_applicable,
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

  fun certify candidate = candidate

  fun elapsed_msec start =
    LargeInt.toInt (Time.toMilliseconds (Time.- (Time.now (), start)))
    handle _ => 0

  fun exhaustive_run (config : Refute_Core.config)
      (problem : Refute_Core.problem) =
    case Refute_Core.preprocess config problem of
        Refute_Core.NotExecutable reasons => Refute_Core.Unknown reasons
      | Refute_Core.Preprocessed instances =>
          let
            val plans = List.map
              (fn instance => compile_plan config (#goal instance))
              instances
          in
            case selected_substrate (#substrate (#qc config)) of
                NONE =>
                  Refute_Core.Unknown ["requested substrate is unavailable"]
              | SOME substrate =>
                  if not (#applicable substrate (problem, plans)) then
                    Refute_Core.Unknown ["not executable"]
                  else
                    let
                      val compiled = #compile substrate config plans
                      val entries = schedule instances (#size (#qc config))
                      val complete = ref (not (null entries))
                      val counterexamples = ref []
                      fun instance_for card =
                        List.nth (instances, card - 1)
                      fun one (card, size) =
                        let
                          val start = Time.now ()
                          val result = #run compiled
                            {genuine_only = #genuine_only config,
                             card = card, size = size}
                          val msec = elapsed_msec start
                        in
                          case result of
                              Exhausted {complete = entry_complete} =>
                                complete := (!complete andalso entry_complete)
                            | GaveUp reason => complete := false
                            | CexFound {env, genuine} =>
                                let
                                  val instance = instance_for card
                                  val bindings = List.filter
                                    (fn (variable, _) =>
                                      List.exists
                                        (fn free => Term.aconv free variable)
                                        (Term.free_vars_lr (#goal instance)))
                                    env
                                  val cex : Refute_Core.counterexample =
                                    { backend = "exhaustive",
                                      certainty = if genuine then
                                        Refute_Core.Potential []
                                      else Refute_Core.Potential
                                        ["evaluation stuck during testing"],
                                      bindings = rev bindings,
                                      evals = [], cert = NONE, scope = NONE,
                                      stats = !last_stats @
                                        [("size", size), ("card", card),
                                         ("msec", msec)] }
                                in
                                  counterexamples :=
                                    certify cex :: !counterexamples
                                end
                        end
                      fun search [] = ()
                        | search (entry :: rest) =
                            if length (!counterexamples) >=
                              Int.max (1, #max_counterexamples config)
                            then ()
                            else (one entry; search rest)
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

  val _ = Refute_Core.register_backend exhaustive_backend
end
