structure Refute_EvalCompute = struct
  type term = Term.term
  open Refute_Cert Refute_Eval
  structure Util = Refute_Util

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

  (* First hit over a value list: run the continuation until it answers. *)
  fun each values continuation =
    List.foldl (fn (value, result) =>
      case result of Continue => continuation value | found => found)
      Continue values

  fun enum_args [] _ continuation = continuation []
    | enum_args (spec :: rest) size continuation =
        exhaustive_values spec size (fn value =>
          case enum_args rest size
            (fn values => continuation (value :: values)) of
              Continue => Continue
            | found => found)

  and exhaustive_function dom rng size continuation =
    case Refute_Gen.enumerate (Type.mk_type ("fun", [dom, rng])) of
        SOME graphs => each graphs continuation
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
        Refute_Gen.GenEnum values => each values continuation
      | Refute_Gen.GenNum kind =>
          each (numeric_terms kind size) continuation
      | Refute_Gen.GenCustom {enumerate = SOME enum, ...} =>
          each (enum size) continuation
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

  fun boolean_value_to_string IsTrue = "true"
    | boolean_value_to_string IsFalse = "false"
    | boolean_value_to_string IsStuck = "stuck"

  fun trace_candidate env result =
    if not (Refute_Core.Private.enabled 4) then ()
    else
      let
        fun binding (variable, value) =
          Parse.term_to_string variable ^ " = " ^ Parse.term_to_string value
        val bindings = String.concatWith ", " (List.map binding (rev env))
        val shown = if bindings = "" then "<closed>" else bindings
      in
        Refute_Core.Private.say 4
          ("Refute compute candidate: " ^ shown ^ " => " ^
           boolean_value_to_string result ^ "\n")
      end

  exception EnumInvalid = Refute_EvalEnum.Invalid

  val prepare_enums = Refute_EvalEnum.prepare

  fun exhaustive_terms ty size =
    case Refute_Gen.enumerate ty of
        SOME values => values
      | NONE =>
          let
            val values = ref []
            val _ = exhaustive_values (Refute_Gen.spec_of ty) size
              (fn value => (values := value :: !values; Continue))
          in
            rev (!values)
          end

  fun match_enum_terms environment patterns values =
    let
      fun match_term additions pattern value =
        if Term.is_var pattern then
          let val bound = additions @ environment in
            (case List.find (fn (old, _) => Term.aconv old pattern) bound of
                 SOME (_, old_value) =>
                   if Term.aconv old_value value then SOME additions else NONE
               | NONE => SOME ((pattern, value) :: additions))
          end
        else if Util.same_type (Term.type_of pattern) numSyntax.num andalso
                  numSyntax.is_numeral value andalso
                  numSyntax.is_suc pattern then
            let val number = numSyntax.dest_numeral value
            in
              if number = Arbnum.zero then NONE
              else match_term additions (numSyntax.dest_suc pattern)
                (numSyntax.mk_numeral (Arbnum.less1 number))
            end
          else
            case (fully_applied_constructor pattern,
                  fully_applied_constructor value) of
                (SOME (pattern_constructor, pattern_args),
                 SOME (value_constructor, value_args)) =>
                  if Term.same_const pattern_constructor value_constructor
                     andalso length pattern_args = length value_args then
                    match_many additions pattern_args value_args
                  else NONE
              | _ =>
                  let val bound = additions @ environment in
                    case eval_rhs bound pattern of
                        SOME expected =>
                          if Term.aconv expected value
                          then SOME additions else NONE
                      | NONE => NONE
                  end
      and match_many additions [] [] = SOME additions
        | match_many additions (pattern :: rest) (value :: values) =
            (case match_term additions pattern value of
                 SOME extended => match_many extended rest values
               | NONE => NONE)
        | match_many _ _ _ = NONE
    in
      Option.map (fn additions => rev additions @ environment)
        (match_many [] patterns values)
    end

  fun enum_program_for programs relation mode =
    case Refute_EvalEnum.find_by_mode Lib.I relation mode programs of
        SOME program => program
      | NONE => raise EnumInvalid
          "smart plan: enumerator dependency is absent"

  fun smart_guard_program programs predicate version =
    Refute_EvalEnum.smart_guard_lookup
      {relation = predicate, version = version} programs

  (* Filtering ignored candidates belongs here rather than in a driver:
     other substrates use different retry protocols. *)
  fun traverse enum_values programs gen genuine_only ignored plan =
    let
      val complete = ref (not (Refute_Eval.plan_uses_enum plan))
      val match_failures = ref 0
      val tests = ref 0

      fun candidate env genuine =
        let
          val found =
            {env = env, ground_env = NONE, case_tree = NONE,
             genuine = genuine, run_depth = NONE}
        in
          if ignored_candidate found ignored then Continue
          else Found found
        end

      fun visit env genuine current =
        case current of
            Prune => Continue
          | Test tm =>
              let
                val _ = tests := !tests + 1
                val result = eval_boolean env tm
                val _ = trace_candidate env result
              in
                case result of
                    IsTrue => Continue
                  | IsFalse =>
                      if genuine orelse not genuine_only then
                        candidate env genuine
                      else Continue
                  | IsStuck =>
                      (complete := false;
                       if genuine_only then Continue
                       else candidate env false)
              end
          | Guard (tm, next) =>
              (case eval_boolean env tm of
                   IsTrue => visit env genuine next
                 | IsFalse => Continue
                 | IsStuck =>
                     (complete := false;
                      if genuine_only then Continue
                      else visit env false next))
          | SmartGuard {predicate, version, cont} =>
              (case smart_guard_program programs predicate version of
                   SOME (program, ins) =>
                     let val inputs = List.map (eval_rhs env) ins
                     in
                       (* [complete] already starts false for any plan that
                          mentions Enum or SmartGuard. *)
                       if List.all Option.isSome inputs then
                         each (enum_values program (List.map valOf inputs))
                           (fn _ => visit env genuine cont)
                       else Continue
                     end
                 | NONE =>
                     (case eval_boolean env predicate of
                          IsTrue => visit env genuine cont
                        | IsFalse => Continue
                        | IsStuck =>
                            (complete := false;
                             if genuine_only then Continue
                             else visit env false cont)))
          | Enum {rel, mode, ins, outs, cont, ...} =>
              let
                val inputs = List.map (eval_rhs env) ins
              in
                if List.all Option.isSome inputs then
                  let
                    val program = enum_program_for programs rel mode
                  in
                    each (enum_values program (List.map valOf inputs))
                      (fn values =>
                        case match_enum_terms env outs values of
                            SOME extended => visit extended genuine cont
                          | NONE => Continue)
                  end
                else Continue
              end
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

  fun exhaustive_compile (config : Refute_Core.config) plans programs =
    let
      val last_stats = ref []
      val enum_cache =
        ref ([] :
          (int * (Refute_EvalEnum.definition * term list)) list)
      val active : Refute_EvalEnum.definition Refute_EvalEnum.held_bracket =
        Refute_EvalEnum.held_bracket (fn () => enum_cache := [])
      val prefix = Refute_EvalEnum.fresh_prefix "refute_compute_enum_"

      fun close () = Refute_EvalEnum.close_held_bracket active

      fun start () = Refute_EvalEnum.start_held_bracket active (fn () =>
        Refute_EvalEnum.define
          {prefix = prefix, programs = programs, after_define = fn _ => ()})

      fun enum_values size program inputs =
        let
          val (data, generators) =
            case List.find (fn (cached_size, _) => cached_size = size)
                (!enum_cache) of
                SOME (_, cached) => cached
              | NONE =>
                  let
                    val data = start ()
                    val generators = map (fn ty =>
                      listSyntax.mk_list (exhaustive_terms ty size, ty))
                      (#generator_types data)
                    val cached = (data, generators)
                    val _ = enum_cache := (size, cached) :: !enum_cache
                  in
                    cached
                  end
          val enumerator = Refute_EvalEnum.enumerator_for
            (#enumerators data) (#relation program) (#mode program)
          val application = Refute_EvalEnum.application enumerator
            generators inputs (Int.max (0, #depth (#qc config)))
          val value =
            case eval_rhs [] application of
                SOME found => found
              | NONE => raise Fail "compute Enum evaluation was stuck"
          val packed = #1 (listSyntax.dest_list value)
        in
          map (fn output => map (fn component =>
            case eval_rhs [] component of
                SOME value => value
              | NONE => component)
            (Refute_EvalEnum.unpack_terms
              (#output_types enumerator) output)) packed
        end

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
                  SOME values => each values try
                | NONE =>
                    (complete := false;
                     exhaustive_values (Refute_Gen.spec_of ty) size try)
            end
          val {result, complete, stats} =
            traverse (enum_values size) programs gen
              genuine_only ignored plan
          val _ = last_stats := stats
        in
          case result of
              Found candidate => CexFound candidate
            | Continue => Exhausted {complete = complete}
        end
        handle Refute_Gen.NoGenerator (_, reason) => GaveUp reason
             | Fail reason => GaveUp reason
             | Feedback.HOL_ERR error =>
                 GaveUp (Feedback.message_of error)
    in
      {run = run, close = close, max_chunk = NONE,
       last_stats = last_stats}
    end

  fun bounded_size size = Int.max (0, size)

  val arbnum_of_intinf = Arbnum.fromLargeInt
  val arbint_of_intinf = Arbint.fromLargeInt

  (* The normative random-consumption discipline, parameterized over the
     draw primitive (and the custom-generator policy) so the cv candidate
     dump can replay exactly the same stream through cv_eval. *)
  fun random_number_with draw Refute_Gen.Num size state =
        let
          val radius = IntInf.fromInt (bounded_size size)
          val bound = radius + 1
          val (value, next) = draw bound state
        in
          (numSyntax.mk_numeral (arbnum_of_intinf value), next)
        end
    | random_number_with draw Refute_Gen.Int size state =
        let
          val radius = IntInf.fromInt (bounded_size size)
          val bound = 2 * radius + 1
          val (value, next) = draw bound state
          val signed = value - radius
        in
          (intSyntax.term_of_int (arbint_of_intinf signed), next)
        end
    | random_number_with draw Refute_Gen.Char _ state =
        let
          val (value, next) = draw 256 state
        in
          (stringSyntax.mk_chr
             (numSyntax.mk_numeral (arbnum_of_intinf value)), next)
        end
    | random_number_with draw (Refute_Gen.Word width) _ state =
        let
          val bound = IntInf.pow (2, width)
          val (value, next) = draw bound state
        in
          (wordsSyntax.mk_wordi (arbnum_of_intinf value, width), next)
        end

  fun random_entry_with draw custom spec size state =
    let
      val floor = Refute_Gen.own_floor spec
    in
      random_value_with draw custom spec
        {budget = Int.max (floor, bounded_size size),
         size = bounded_size size} state
    end

  and random_args_with _ _ [] [] _ _ state = ([], state)
    | random_args_with draw custom (ty :: tys)
        (is_recursive :: recursive) budget size state =
        let
          val (value, next) =
            if is_recursive then
              random_value_with draw custom (Refute_Gen.spec_of ty)
                {budget = Int.max (0, budget - 1), size = size} state
            else
              random_entry_with draw custom (Refute_Gen.spec_of ty)
                size state
          val (values, final) =
            random_args_with draw custom tys recursive budget size next
        in
          (value :: values, final)
        end
    | random_args_with _ _ _ _ _ _ _ =
        raise Fail "Refute_QC.random_args: malformed datatype"

  and random_function_with draw custom dom rng_ty size state =
    let
      val entry = random_entry_with draw custom
      val variable = Term.mk_var ("x", dom)
      val (default, after_default) =
        entry (Refute_Gen.spec_of rng_ty) size state
      fun draw_points 0 current = ([], current)
        | draw_points count current =
            let
              val (point, next) =
                entry (Refute_Gen.spec_of dom) size current
              val (points, final) = draw_points (count - 1) next
            in
              (point :: points, final)
            end
      val (points, after_points) =
        case Refute_Gen.enumerate dom of
            SOME values => (values, after_default)
          | NONE => draw_points (bounded_size size) after_default
      fun add (point, (base, current)) =
        let
          val (value, next) =
            entry (Refute_Gen.spec_of rng_ty) size current
        in
          (Term.mk_comb (combinSyntax.mk_update (point, value), base), next)
        end
      val (result, final) = List.foldl add
        (Term.mk_abs (variable, default), after_points) points
    in
      (result, final)
    end

  and random_value_with draw custom spec {budget, size} state =
    case spec of
        Refute_Gen.GenEnum values =>
          if null values then
            raise Fail "Refute_QC.random_value: empty enumeration"
          else
            let
              val (choice, next) =
                draw (IntInf.fromInt (length values)) state
            in
              (List.nth (values, IntInf.toInt choice), next)
            end
      | Refute_Gen.GenNum kind => random_number_with draw kind size state
      | Refute_Gen.GenCustom {random, ...} => custom random size state
      | Refute_Gen.GenFun (dom, rng_ty) =>
          random_function_with draw custom dom rng_ty size state
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
            val total = List.foldl (fn ((_, _, value), sum) =>
              IntInf.fromInt value + sum) 0 choices
            val (choice, after_choice) = draw total state
            fun select _ [] =
                  raise Fail
                    "Refute_QC.random_value: no constructor"
              | select remaining ((constructor, flags, value) :: rest) =
                  let val weight = IntInf.fromInt value
                  in
                    if remaining < weight then (constructor, flags)
                    else select (remaining - weight) rest
                  end
            val ((constructor, arg_types), flags) = select choice choices
            val (arguments, final) = random_args_with draw custom
              arg_types flags budget size after_choice
          in
            (Term.list_mk_comb (constructor, arguments), final)
          end

  fun default_custom (SOME generate) size state = generate size state
    | default_custom NONE _ _ =
        raise Fail "Refute_QC.random_value: no random generator"

  fun random_entry spec =
    random_entry_with checked_rand_below default_custom spec

  fun random_value spec =
    random_value_with checked_rand_below default_custom spec

  fun random_term ty size state =
    random_entry (Refute_Gen.spec_of ty) size state

  fun stat name stats =
    Option.getOpt (Refute_Core.lookup_stat name stats, 0)

  fun random_gen state size visit _ env genuine variable next =
    let
      val (value, after_draw) =
        random_term (Term.type_of variable) size (!state)
      val _ = state := after_draw
    in
      visit ((variable, value) :: env) genuine next
    end

  fun random_compile plans state =
    let
      val last_stats = ref []
      fun run {genuine_only, card, size, draws, ignored} =
        let
          val plan = List.nth (plans, card - 1)
          val tests = ref 0
          val match_failures = ref 0
          val all_complete = ref true

          fun attempt 0 = Exhausted {complete = !all_complete}
            | attempt remaining =
                let
                  val {result, complete, stats} =
                    traverse (fn _ => fn _ => []) []
                      (random_gen state size) genuine_only ignored plan
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
      {run = run, close = fn () => (), max_chunk = NONE,
       last_stats = last_stats}
    end

  (* Compute-only scaffolding for the cross-substrate stream tests.  One
     result records, in order, every Gen draw made by one plan attempt. *)
  fun dump_random_candidates {plan, seed, size, count} =
    let
      val state = ref seed

      fun one () =
        let
          val generated = ref []
          fun gen visit _ env genuine variable next =
            let
              val (value, after_draw) =
                random_term (Term.type_of variable) size (!state)
              val _ = state := after_draw
              val _ = generated := value :: !generated
            in
              visit ((variable, value) :: env) genuine next
            end
          val _ = traverse (fn _ => fn _ => []) [] gen false [] plan
        in
          rev (!generated)
        end

      fun loop 0 candidates = rev candidates
        | loop remaining candidates =
            loop (remaining - 1) (one () :: candidates)
    in
      loop (bounded_size count) []
    end

  fun no_generator_reason ty why =
    "no generator for " ^ Parse.type_to_string ty ^ " \226\128\148 " ^ why

  fun validation_reasons strategy plans programs =
    let
      val seen = ref []
      val reasons = ref []

      fun add reason =
        if List.exists (fn old => old = reason) (!reasons) then ()
        else reasons := reason :: !reasons

      fun validate_type ty =
        if Util.member_type ty (!seen) then ()
        else
          let
            val _ = seen := ty :: !seen
            val spec = Refute_Gen.spec_of ty
          in
            case spec of
                Refute_Gen.GenEnum _ => ()
              | Refute_Gen.GenNum (Refute_Gen.Word width) =>
                  ground_strategy strategy
                    {exhaustive = fn () => (),
                     random = fn _ =>
                       if width <= 32 then ()
                       else add (no_generator_reason ty
                         "word width exceeds rand_below's 32-bit bound")}
              | Refute_Gen.GenNum _ => ()
              | Refute_Gen.GenFun (dom, rng) =>
                  (validate_type dom; validate_type rng)
              | Refute_Gen.GenDatatype {constrs, ...} =>
                  List.app validate_type
                    (List.concat (List.map #2 constrs))
              | Refute_Gen.GenCustom {enumerate, random} =>
                  ground_strategy strategy
                    {exhaustive = fn () =>
                       if Option.isSome enumerate then ()
                       else add (no_generator_reason ty
                         "custom generator has no enumeration arm"),
                     random = fn _ =>
                       if Option.isSome random then ()
                       else add (no_generator_reason ty
                         "custom generator has no random arm")}
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
          | SmartGuard {cont, ...} => validate_plan cont
          | Enum {cont, ...} => validate_plan cont
          | Prune => ()
      val _ = List.app validate_plan plans
      val _ = List.app validate_type
        (Refute_EvalEnum.generator_types programs)
    in
      rev (!reasons)
    end

  fun compile (config : Refute_Core.config) strategy problem =
    with_plans problem (fn plans =>
      let
        (* Both testing strategies share the enumerator preparation and
           validation; only the loop built from the result differs. *)
        fun attempt build =
          (let
             val programs = prepare_enums strategy plans
           in
             case validation_reasons strategy plans programs of
                 [] => Compiled (build programs)
               | reasons => Inapplicable reasons
           end)
          handle EnumInvalid reason => Inapplicable [reason]
      in
        ground_strategy strategy
          {exhaustive = fn () =>
             attempt (exhaustive_compile config plans),
           random = fn seed =>
             attempt (fn _ => random_compile plans (ref seed))}
      end)

  val compute_substrate : substrate =
    { name = "compute",
      priority = 30,
      accepts = (fn Plans _ => true | Pnf _ => false),
      preflight = NONE,
      compile = compile }

  fun register_substrate () =
    Refute_Eval.register_substrate compute_substrate

  val _ = register_substrate ()
end
