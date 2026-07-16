structure Refute_EvalCompute = struct
  type term = Term.term
  open Refute_Cert Refute_Eval

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

  (* Filtering ignored candidates belongs here rather than in a driver:
     other substrates use different retry protocols. *)
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
        stats = [
          ("tests", !tests),
          ("match_failures", !match_failures)] }
    end

  fun exhaustive_compile plans =
    let
      val last_stats = ref []
      fun run {genuine_only, card, size, draws, ignored} =
        let
          val _ = draws
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
        raise Fail "Refute_QC.random_args: malformed datatype"

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
                  raise Fail
                    "Refute_QC.random_value: malformed datatype"
            val choices = entries constrs recursive min_size
            val total = List.foldl (fn ((_, _, value), sum) => sum + value)
              0 choices
            val choice = Random.range (0, total) rng
            fun select _ [] =
                  raise Fail
                    "Refute_QC.random_value: no constructor"
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

  fun stat name stats =
    case List.find (fn (key, _) => key = name) stats of
        NONE => 0
      | SOME (_, value) => value

  fun random_compile plans rng =
    let
      val last_stats = ref []
      fun run {genuine_only, card, size, draws, ignored} =
        let
          val plan = List.nth (plans, card - 1)
          val tests = ref 0
          val match_failures = ref 0
          val all_complete = ref true

          fun gen visit _ env genuine variable next =
            let
              val (value, _) =
                random_term (Term.type_of variable) size rng
            in
              visit ((variable, value) :: env) genuine next
            end

          fun attempt 0 = Exhausted {complete = !all_complete}
            | attempt remaining =
                let
                  val {result, complete, stats} =
                    traverse gen genuine_only ignored plan
                  val _ = tests := !tests + stat "tests" stats
                  val _ = match_failures := !match_failures +
                    stat "match_failures" stats
                  val _ = all_complete := (!all_complete andalso complete)
                in
                  case result of
                      Found candidate => CexFound candidate
                    | Continue => attempt (remaining - 1)
                end

          val result =
            (attempt (bounded_size draws)
             handle Refute_Gen.NoGenerator (_, reason) => GaveUp reason
                  | Fail reason => GaveUp reason)
          val _ = last_stats := [
            ("tests", !tests),
            ("match_failures", !match_failures)]
        in
          result
        end
    in
      {run = run, last_stats = last_stats}
    end

  fun same_type ty1 ty2 = Type.compare (ty1, ty2) = EQUAL

  fun no_generator_reason ty why =
    "no generator for " ^ Parse.type_to_string ty ^ " \226\128\148 " ^ why

  fun validation_reasons strategy plans =
    let
      val seen = ref []
      val reasons = ref []

      fun add reason =
        if List.exists (fn old => old = reason) (!reasons) then ()
        else reasons := reason :: !reasons

      fun validate_type ty =
        if List.exists (same_type ty) (!seen) then ()
        else
          let
            val _ = seen := ty :: !seen
            val spec = Refute_Gen.spec_of ty
          in
            case spec of
                Refute_Gen.GenEnum _ => ()
              | Refute_Gen.GenNum _ => ()
              | Refute_Gen.GenFun (dom, rng) =>
                  (validate_type dom; validate_type rng)
              | Refute_Gen.GenDatatype {constrs, ...} =>
                  List.app validate_type
                    (List.concat (List.map #2 constrs))
              | Refute_Gen.GenCustom {enumerate, random} =>
                  (case strategy of
                     Exhaustive =>
                       if Option.isSome enumerate then ()
                       else add (no_generator_reason ty
                         "custom generator has no enumeration arm")
                   | Random _ =>
                       if Option.isSome random then ()
                       else add (no_generator_reason ty
                         "custom generator has no random arm"))
          end
          handle Refute_Gen.NoGenerator (missing_ty, why) =>
            add (no_generator_reason missing_ty why)

      fun validate_plan current =
        case current of
            Test _ => ()
          | Gen (variable, next) =>
              (validate_type (Term.type_of variable); validate_plan next)
          | Bind (_, _, fallback, next) =>
              ((case fallback of
                  NONE => ()
                | SOME alternative => validate_plan alternative);
               validate_plan next)
          | Split (_, branches) =>
              List.app (fn (_, _, next) => validate_plan next) branches
          | Guard (_, next) => validate_plan next
          | Prune => ()
      val _ = List.app validate_plan plans
    in
      rev (!reasons)
    end

  fun random_generator (config : Refute_Core.config) seed =
    case #seed (#qc config) of
        SOME _ => Random.newgenseed (Real.fromLargeInt seed)
      | NONE => !session_rng

  fun compile (config : Refute_Core.config) strategy plans =
    case validation_reasons strategy plans of
        [] =>
          Compiled
            (case strategy of
               Exhaustive => exhaustive_compile plans
             | Random {seed} =>
                 random_compile plans (random_generator config seed))
      | reasons => Inapplicable reasons

  val compute_substrate : substrate =
    { name = "compute",
      priority = 30,
      compile = compile }

  fun register_substrate () =
    Refute_Eval.register_substrate compute_substrate

  val _ = register_substrate ()
end
