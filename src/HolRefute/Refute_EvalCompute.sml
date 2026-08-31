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

  fun bounded_power_of_two width limit =
    let
      fun loop 0 total = total
        | loop remaining total =
            if total >= limit orelse total > limit div 2 then limit
            else loop (remaining - 1) (2 * total)
    in
      if width <= 0 then 1 else loop width 1
    end

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
        let
          (* Finite word types within the enumeration cap are enums even
             when nested below a datatype constructor. *)
          val count = if width <= 8 then bounded_power_of_two width 257
                      else bounded_power_of_two width
                        (Int.max (0, size) + 1)
        in
          List.tabulate (count,
            fn index => wordsSyntax.mk_wordii (index, width))
        end

  (* The generator half shared by every fraction-shaped carrier
     ([:rat], [:real]): only the literal constructor differs, so the
     sampling and enumeration policy is stated once here rather than
     once per carrier.  Numerators span [-size, size], the house GenNum
     Int convention above; denominators are drawn as k + 1 for k in
     [0, size], so every candidate is well-formed by construction and no
     draw can reach a zero or negative denominator.  Enumeration is
     restricted to lowest terms (0 admitted only as 0/1): every distinct
     fraction at this radius is covered exactly once instead of via
     every non-reduced form that also fits, which only changes ordering,
     pinned nowhere. *)
  fun fraction_generator mk_lit : Refute_Gen.custom_gen =
    let
      fun draw_numerator size state =
        let
          val radius = IntInf.fromInt (Int.max (0, size))
          val bound = 2 * radius + 1
          val (value, next) = Refute_Eval.checked_rand_below bound state
        in
          (IntInf.toInt value - IntInf.toInt radius, next)
        end

      fun draw_denominator size state =
        let
          val bound = IntInf.fromInt (Int.max (0, size) + 1)
          val (value, next) = Refute_Eval.checked_rand_below bound state
        in
          (IntInf.toInt value + 1, next)
        end

      fun random size state =
        let
          val (n, s1) = draw_numerator size state
          val (d, s2) = draw_denominator size s1
        in
          (mk_lit (n, d), s2)
        end

      fun gcd (a, 0) = a
        | gcd (a, b) = gcd (b, a mod b)

      fun in_lowest_terms (0, d) = (d = 1)
        | in_lowest_terms (n, d) = gcd (Int.abs n, d) = 1

      fun enumerate size =
        let val radius = Int.max (0, size)
        in
          List.concat
            (List.tabulate (radius + 1, fn k =>
              let val d = k + 1
              in
                List.mapPartial
                  (fn i =>
                     let val n = i - radius
                     in
                       if in_lowest_terms (n, d) then SOME (mk_lit (n, d))
                       else NONE
                     end)
                  (List.tabulate (2 * radius + 1, fn i => i))
              end))
        end
    in
      {enumerate = SOME enumerate, random = SOME random}
    end

  fun checked_custom_value expected value =
    if Util.same_type (Term.type_of value) expected then value
    else
      raise Fail ("Refute_EvalCompute: custom generator for " ^
        Parse.type_to_string expected ^ " returned a value of type " ^
        Parse.type_to_string (Term.type_of value))

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
      | Refute_Gen.GenCustom (ty, {enumerate = SOME enum, ...}) =>
          each (List.map (checked_custom_value ty) (enum size)) continuation
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
      (* [candidates_generated] counts every candidate reaching a terminal
         decision, exactly once, on whichever branch ends it without
         recursing further: a Test visit, a Guard rejection (false, or
         given up on stuck), a SmartGuard rejection (compiled-relation
         empty result, ungrounded inputs, or -- on the eval_boolean
         fallback -- false or given up on stuck, mirroring Guard), an
         Enum branch whose inputs were not yet ground or that could not
         match a generated value, a Bind whose value computation got
         stuck (fallback-less or given up on stuck), or a Split that
         could not classify its scrutinee, found no matching branch, or
         could not even evaluate its scrutinee.  A branch that recurses
         (visits [next]/[cont]) never increments here itself -- the
         recursive visit's own terminal branch does, so nothing is
         double-counted.  [Prune] is excluded: the planner already knows
         that branch can never fire, so nothing was generated to count.
         [assumption_satisfied] counts only Test visits with [genuine]
         true -- no earlier Guard/SmartGuard/Bind/Split step was stuck --
         since a Test can be reached with an undecided premise on the
         genuine-only-false recovery path.  [conclusion_evaluated] further
         excludes IsStuck results, keeping conclusions <= assumptions
         <= candidates. *)
      val candidates_generated = ref 0
      val assumption_satisfied = ref 0
      val conclusion_evaluated = ref 0

      (* The one spelling of "this branch ended a candidate": every
         terminal branch above routes through it, so the counting rule
         stated above is enforced in one place rather than restated at
         each site. *)
      fun dropped () =
        (candidates_generated := !candidates_generated + 1; Continue)

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
                val _ = candidates_generated := !candidates_generated + 1
                val _ =
                  if genuine then
                    assumption_satisfied := !assumption_satisfied + 1
                  else ()
                val result = eval_boolean env tm
                val _ = trace_candidate env result
                val _ =
                  if genuine andalso result <> IsStuck then
                    conclusion_evaluated := !conclusion_evaluated + 1
                  else ()
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
          | Guard {condition, cont, ...} =>
              (* A stuck condition, complement or not, must not be read
                 as a decided [false]. *)
              (case eval_boolean env condition of
                   IsTrue => visit env genuine cont
                 | IsFalse => dropped ()
                 | IsStuck =>
                     (complete := false;
                      if genuine_only then dropped ()
                      else visit env false cont))
          | SmartGuard {predicate, version, cont} =>
              (case smart_guard_program programs predicate version of
                   SOME (program, ins) =>
                     let val inputs = List.map (eval_rhs env) ins
                     in
                       (* [complete] already starts false for any plan that
                          mentions Enum or SmartGuard. *)
                       (* A smart Guard binds no outputs, so it is an
                          existence test: the continuation runs once, as on
                          the cv and native substrates. *)
                       if List.all Option.isSome inputs then
                         if null (enum_values program
                                    (List.map valOf inputs)) then
                           dropped ()
                         else visit env genuine cont
                       else
                         dropped ()
                     end
                 | NONE =>
                     (case eval_boolean env predicate of
                          IsTrue => visit env genuine cont
                        | IsFalse => dropped ()
                        | IsStuck =>
                            (complete := false;
                             if genuine_only then dropped ()
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
                          | NONE => dropped ())
                  end
                else
                  dropped ()
              end
          | Bind (variable, tm, fallback, next) =>
              (case eval_rhs env tm of
                   SOME value =>
                     visit ((variable, value) :: env) genuine next
                 | NONE =>
                     (complete := false;
                      case fallback of
                          NONE => dropped ()
                        | SOME alternative =>
                            if genuine_only then
                              dropped ()
                            else visit env false alternative))
          | Split (tm, branches) =>
              (case eval_rhs env tm of
                   SOME value =>
                     (case fully_applied_constructor value of
                          NONE =>
                            (complete := false;
                             match_failures := !match_failures + 1;
                             dropped ())
                        | SOME (constructor, args) =>
                            (case List.find (fn (expected, variables, _) =>
                              Term.same_const expected constructor andalso
                              length variables = length args) branches of
                                 (* A partial split is the false constructor
                                    premise, not an evaluator failure. *)
                                 NONE => dropped ()
                               | SOME (_, variables, next) =>
                                   visit
                                     (ListPair.zip (variables, args) @ env)
                                     genuine next))
                 | NONE =>
                     (complete := false;
                      match_failures := !match_failures + 1;
                      dropped ()))
          | Gen (variable, next) =>
              gen visit complete env genuine variable next
      val result = visit [] true plan
    in
      { result = result,
        complete = !complete,
        stats = [
          ("tests", !tests),
          ("match_failures", !match_failures),
          ("assumption_satisfied", !assumption_satisfied),
          ("conclusion_evaluated", !conclusion_evaluated),
          ("candidates_generated", !candidates_generated)] }
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

  (* [hard] is the recursion fuel, [size] the structural budget; they part
     company only below a function boundary, which decays them separately. *)
  fun random_entry_hard_with draw custom spec hard size state =
    random_value_with draw custom spec
      {budget = Int.max (Refute_Gen.own_floor spec, bounded_size size),
       hard_budget = bounded_size hard,
       size = bounded_size size} state

  and random_entry_with draw custom spec size state =
    random_entry_hard_with draw custom spec size size state

  and random_args_with _ _ [] [] _ _ _ state = ([], state)
    | random_args_with draw custom (ty :: tys)
        (is_recursive :: recursive) budget hard_budget size state =
        let
          val (value, next) =
            if is_recursive then
              random_value_with draw custom (Refute_Gen.spec_of ty)
                {budget = Int.max (0, budget - 1),
                 hard_budget = Int.max (0, hard_budget - 1),
                 size = size} state
            else
              (* Preserve the current constructor budget through wrappers
                 such as option.  Resetting it to [size] here lets an
                 indirect recursive field evade the direct-recursion check. *)
              random_value_with draw custom (Refute_Gen.spec_of ty)
                {budget = Int.max (Refute_Gen.own_floor
                   (Refute_Gen.spec_of ty), budget),
                 hard_budget = hard_budget, size = size} state
          val (values, final) =
            random_args_with draw custom tys recursive budget hard_budget
              size next
        in
          (value :: values, final)
        end
    | random_args_with _ _ _ _ _ _ _ _ =
        raise Fail "Refute_QC.random_args: malformed datatype"

  and random_function_with draw custom dom rng_ty hard_budget size state =
    let
      val entry = random_entry_hard_with draw custom
      (* Size and hard recursion fuel decay geometrically across every
         function boundary.  The structural budget may still rise to a
         result type's minimum inhabitation floor, but [hard_budget] never
         does; once it reaches 0, constructors recursive beneath a function
         are disabled while a minimum finite base path remains available.
         Thus a positive [own_floor] cannot replenish recursion and turn a
         function result into an unbounded branching process.  [size div 2]
         and
         [Int.max (0, size - 1)] agree at sizes 0, 1 and 2, so this only
         changes the stream from size 3 up; the faster decay cuts the
         expected node count of the branching process this drives by
         several orders of magnitude at the default size (10), where a
         decay of 1 leaves it supercritical enough to routinely exhaust
         the search deadline instead of terminating.  The point count
         itself stays keyed to the pre-decay [size]. *)
      val decayed = size div 2
      val decayed_hard = hard_budget div 2
      val variable = Term.mk_var ("x", dom)
      val (default, after_default) =
        entry (Refute_Gen.spec_of rng_ty) decayed_hard decayed state
      fun draw_points 0 current = ([], current)
        | draw_points count current =
            let
              val (point, next) =
                entry (Refute_Gen.spec_of dom) decayed_hard decayed current
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
            entry (Refute_Gen.spec_of rng_ty) decayed_hard decayed current
        in
          (Term.mk_comb (combinSyntax.mk_update (point, value), base), next)
        end
      val (result, final) = List.foldl add
        (Term.mk_abs (variable, default), after_points) points
    in
      (result, final)
    end

  and random_value_with draw custom spec {budget, hard_budget, size} state =
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
      | Refute_Gen.GenCustom (ty, {random, ...}) =>
          let val (value, next) = custom random size state
          in (checked_custom_value ty value, next) end
      | Refute_Gen.GenFun (dom, rng_ty) =>
          random_function_with draw custom dom rng_ty hard_budget size state
      | Refute_Gen.GenDatatype
          {constrs, recursive, min_size, fun_recursive, ...} =>
          let
            fun weight (flags, floors, fun_rec) =
              if hard_budget = 0 andalso fun_rec then 0
              else if not (List.exists (fn flag => flag) flags) then 1
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
            fun entries [] [] [] [] = []
              | entries (constr :: rest) (flags :: more_flags)
                  (floors :: more_floors) (fun_rec :: more_fun_rec) =
                  let val entry =
                    (constr, flags, weight (flags, floors, fun_rec))
                  in
                    entry :: entries rest more_flags more_floors more_fun_rec
                  end
              | entries _ _ _ _ =
                  raise Fail
                    "Refute_QC.random_value: malformed datatype"
            val choices = entries constrs recursive min_size fun_recursive
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
              arg_types flags budget hard_budget size after_choice
          in
            (Term.list_mk_comb (constructor, arguments), final)
          end

  fun default_custom (SOME generate) size state = generate size state
    | default_custom NONE _ _ =
        raise Fail "Refute_QC.random_value: no random generator"

  fun random_entry spec =
    random_entry_with checked_rand_below default_custom spec

  fun random_value spec {budget, size} state =
    random_value_with checked_rand_below default_custom spec
      {budget = budget, hard_budget = budget, size = size} state

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
          val assumption_satisfied = ref 0
          val conclusion_evaluated = ref 0
          val candidates_generated = ref 0
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
                  val _ = assumption_satisfied := !assumption_satisfied +
                    stat "assumption_satisfied" stats
                  val _ = conclusion_evaluated := !conclusion_evaluated +
                    stat "conclusion_evaluated" stats
                  val _ = candidates_generated := !candidates_generated +
                    stat "candidates_generated" stats
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
            ("match_failures", !match_failures),
            ("assumption_satisfied", !assumption_satisfied),
            ("conclusion_evaluated", !conclusion_evaluated),
            ("candidates_generated", !candidates_generated)]
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
              | Refute_Gen.GenDatatype {constrs, fun_recursive, ...} =>
                  (ground_strategy strategy
                     {exhaustive = fn () =>
                        if List.exists (fn flag => flag) fun_recursive
                        then add (no_generator_reason ty
                          "datatype is recursive under a function type")
                        else (),
                      random = fn _ => ()};
                   List.app validate_type
                     (List.concat (List.map #2 constrs)))
              | Refute_Gen.GenCustom (_, {enumerate, random}) =>
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
          | Guard {cont, ...} => validate_plan cont
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
