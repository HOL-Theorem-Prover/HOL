open HolKernel Parse boolLib bossLib

(* Shared HOL synthesis for depth-bounded SmartGen enumerators.  Both the
   compute and cv substrates define these equations; only their evaluator of
   the resulting constants differs. *)
structure Refute_EvalEnum = struct
  type term = Term.term
  type hol_type = Type.hol_type
  structure Util = Refute_Util

  exception Invalid of string
  exception CleanupFailed of exn

  (* Private deterministic fault-injection seam.  Tests arm it only while
     checking cleanup after the definition (and cv translation) has landed;
     production leaves it at NONE. *)
  val post_definition_failure_hook =
    ref (NONE : (Thm.thm -> unit) option)

  fun reject message = raise Invalid ("smart plan: " ^ message)

  fun same_program
        ({relation = left, mode = left_mode, version = left_version, ...} :
          Refute_SmartGen.enumerator)
        ({relation = right, mode = right_mode, version = right_version, ...} :
          Refute_SmartGen.enumerator) =
    Refute_SmartGen.same_relation left right andalso
    Refute_SmartGen.eq_mode (left_mode, right_mode) andalso
    Refute_SmartGen.same_program_version (left_version, right_version)

  fun find_by_mode key_projection relation mode items =
    List.find (fn item =>
      let
        val {relation = other, mode = other_mode, ...} :
          Refute_SmartGen.enumerator = key_projection item
      in
        Refute_SmartGen.same_relation relation other andalso
        Refute_SmartGen.eq_mode (mode, other_mode)
      end) items

  fun smart_guard_lookup {relation = predicate, version} programs =
    let
      val (relation, arguments) = HolKernel.strip_comb predicate
      fun inspect [] = NONE
        | inspect (program :: rest) =
            if Refute_SmartGen.same_relation
                 relation (#relation program) andalso
               Refute_SmartGen.same_program_version
                 (version, #version program)
            then
              (case Refute_SmartGen.top_level_parts
                      (#mode program) arguments of
                   SOME (ins, []) => SOME (program, ins)
                 | _ => inspect rest)
            else inspect rest
    in
      inspect programs
    end
    handle Feedback.HOL_ERR _ => NONE

  (* Dependency closure of an enumerator program.  The native extractor
     resolves programs from its own snapshot and gates smart Guards
     differently from the compute/cv path, so the lookups are parameters;
     [reject] raises, and its result is only wrapped to keep one type.

     [dependency]'s production caller ([prepare]'s [lookup]) resolves a
     [CpsCall] purely by relation and mode, with no
     [same_program_version] check -- the one consumption path that omits
     one, because a dependency on an already-compiled *external*
     relation legitimately comes from a different inference with a
     different fingerprint, and a version check would wrongly reject
     that valid case.  What keeps this lookup sound for a [Fixed]
     position is therefore entirely [Refute_SmartGen.eq_mode]'s [Fixed]
     arm: it compares by exact term equality, so a call needing the
     program compiled for [n = 7] cannot resolve here to one compiled
     for [n = 500] even though neither carries a version distinguishing
     them. *)
  fun program_closure reject dependency program programs =
    let
      fun visit program programs =
        if List.exists (same_program program) programs then programs
        else
          let
            val programs = programs @ [program]
            fun calls (Refute_SmartGen.CpsClause {premises, ...}) =
              List.mapPartial
                (fn Refute_SmartGen.CpsCall {rel, mode, ...} =>
                      (case dependency rel mode of
                           SOME found => SOME found
                         | NONE => SOME (reject
                             "missing recursive enumerator dependency"))
                  | _ => NONE) premises
          in
            List.foldl (fn (found, result) => visit found result) programs
              (List.concat (map calls (#clauses program)))
          end
    in
      visit program programs
    end

  (* Every enumerator program a plan needs, in dependency-closed order. *)
  fun collect_programs reject dependency top_program guard_program =
    let
      val closure = program_closure reject dependency
      fun collect current programs =
        case current of
            Refute_Eval.Test _ => programs
          | Refute_Eval.Gen (_, next) => collect next programs
          | Refute_Eval.Bind (_, _, fallback, next) =>
              collect next (case fallback of NONE => programs
                | SOME alternative => collect alternative programs)
          | Refute_Eval.Split (_, branches) =>
              List.foldl (fn ((_, _, next), result) =>
                collect next result) programs branches
          | Refute_Eval.Guard (_, next) => collect next programs
          | Refute_Eval.NegGuard (_, next) => collect next programs
          | Refute_Eval.SmartGuard {predicate, version, cont} =>
              collect cont
                (closure (guard_program predicate version) programs)
          | Refute_Eval.Enum {rel, mode, version, cont, ...} =>
              collect cont (closure (top_program rel mode version) programs)
          | Refute_Eval.Prune => programs
    in
      collect
    end

  fun mode_shape_with reject relation mode =
    let
      fun rejected message =
        (reject message;
         raise Fail
           "Refute_EvalEnum.mode_shape_with: rejecting function returned")
    in
      (let
         val _ = if Term.is_const relation then ()
           else rejected "enumerator relation is not a constant"
         val (domains, range) = boolSyntax.strip_fun (Term.type_of relation)
         val modes = Refute_SmartGen.strip_mode mode
         val _ = if Util.same_type range Type.bool then ()
           else rejected "enumerator relation does not return bool"
         val _ = if length domains = length modes andalso
             List.all Refute_SmartGen.first_order_mode modes then ()
           else rejected "enumerator mode/arity mismatch"
         (* A [Fixed] position's own [split_arguments] arm verifies the
            actual term against the pinned value ([Refute_SmartGen]'s
            [split_atomic]), so a synthetic placeholder there always
            fails that check.  This is a shape probe only -- no real call
            site is in scope -- so use the pinned value itself at that
            position; every other position still gets a fresh, distinctly
            named placeholder. *)
         val arguments = Lib.mapi (fn index => fn ty =>
           case List.nth (modes, index) of
               Refute_SmartGen.Fixed value => value
             | _ => Term.mk_var
                 ("refute_enum_shape_" ^ Int.toString index, ty)) domains
         val (ins, outs) = Refute_SmartGen.split_arguments mode arguments
       in
         (map Term.type_of ins, map Term.type_of outs)
       end
       handle Feedback.HOL_ERR _ =>
         rejected "enumerator mode/type mismatch")
    end

  fun mode_shape relation mode = mode_shape_with reject relation mode

  val same_types = Lib.list_eq Util.same_type

  fun special_literal tm =
    Literal.is_numeral tm orelse intSyntax.is_int_literal tm orelse
    Literal.is_char_lit tm orelse Literal.is_string_lit tm orelse
    oneSyntax.is_one tm orelse wordsSyntax.is_word_literal tm orelse
    Term.aconv tm boolSyntax.T orelse Term.aconv tm boolSyntax.F

  (* This is the single validation policy for every smart-plan consumer.
     Callers choose only their exception through [reject]; all structural and
     executability checks deliberately have the same strength everywhere. *)
  fun validate reject programs plans =
    let
      fun rejected message =
        (reject message;
         raise Fail "Refute_EvalEnum.validate: rejecting function returned")
      fun vars_bound bound tm =
        List.all (fn variable => List.exists (fn old =>
          Term.aconv old variable) bound) (Term.free_vars_lr tm)
      fun require_bound label bound terms =
        if List.all (vars_bound bound) terms then ()
        else rejected (label ^ " uses an unbound variable")
      fun fresh_in bound variable =
        not (Util.aconv_member variable bound)

      fun validate_executable label consumed terms =
        let
          val constants = Refute_Core.nonexecutable_constants terms
          val remaining = List.filter (fn constant =>
            not (List.exists (fn allowed =>
              Term.same_const allowed constant) consumed)) constants
          val has_binder =
            List.exists Refute_Core.has_unexpanded_binder terms
        in
          if has_binder then
            rejected (label ^ " contains an unexpanded binder")
          else if null remaining then ()
          else rejected (label ^ " is nonexecutable: " ^
            Refute_Core.show_constants remaining)
        end

      fun validate_patterns label bound patterns =
        let
          fun pattern (tm, current) =
            if Term.is_var tm then
              if fresh_in current tm then current @ [tm] else current
            else if special_literal tm then current
            else
              case Refute_Eval.fully_applied_constructor tm of
                  SOME (_, arguments) =>
                    List.foldl pattern current arguments
                | NONE =>
                    (require_bound label current [tm];
                     validate_executable label [] [tm]; current)
        in
          List.foldl pattern bound patterns
        end

      fun require_boolean label tm =
        if Util.same_type (Term.type_of tm) Type.bool then ()
        else rejected (label ^ " does not have type bool")

      fun program_for relation mode =
        case find_by_mode Lib.I relation mode programs of
            SOME program => program
          | NONE => rejected "enumerator dependency is absent"

      fun validate_program
            ({relation, mode, clauses, ...} : Refute_SmartGen.enumerator) =
        let
          val (input_types, output_types) =
            mode_shape_with rejected relation mode
          fun premise (item, current) =
            case item of
                Refute_SmartGen.CpsGenerate variable =>
                  if Term.is_var variable andalso fresh_in current variable
                  then current @ [variable]
                  else rejected
                    "generator variable is malformed or already bound"
              | Refute_SmartGen.CpsGuard tm =>
                  (require_bound "enumerator Guard" current [tm];
                   require_boolean "enumerator Guard" tm;
                   validate_executable "enumerator Guard" [] [tm]; current)
              | Refute_SmartGen.CpsCall {rel, mode, ins, outs} =>
                  let
                    val _ = program_for rel mode
                    val (expected_ins, expected_outs) =
                      mode_shape_with rejected rel mode
                    val _ = if same_types (map Term.type_of ins) expected_ins
                        andalso same_types
                          (map Term.type_of outs) expected_outs then ()
                      else rejected "recursive call mode/arity/types mismatch"
                    val _ = require_bound "recursive call input" current ins
                    val _ = validate_executable
                      "recursive call input" [] ins
                  in
                    validate_patterns "recursive call output" current outs
                  end
          fun clause (Refute_SmartGen.CpsClause
                {ins, premises, outs}) =
            let
              val _ = if same_types (map Term.type_of ins) input_types
                  andalso same_types (map Term.type_of outs) output_types
                then () else rejected "clause mode/arity/types mismatch"
              val initial = validate_patterns "clause input" [] ins
              val current = List.foldl premise initial premises
              val _ = require_bound "clause output" current outs
              val _ = validate_executable "clause output" [] outs
            in
              ()
            end
        in
          List.app clause clauses
        end
      val _ = List.app validate_program programs

      fun validate_plan current bound =
        case current of
            Refute_Eval.Test tm =>
              (require_bound "Test" bound [tm];
               require_boolean "Test" tm;
               validate_executable "Test" [] [tm])
          | Refute_Eval.Gen (variable, next) =>
              if Term.is_var variable andalso fresh_in bound variable then
                validate_plan next (variable :: bound)
              else rejected "Gen variable is malformed or already bound"
          | Refute_Eval.Bind (variable, tm, fallback, next) =>
              (require_bound "Bind expression" bound [tm];
               validate_executable "Bind expression" [] [tm];
               if Term.is_var variable andalso fresh_in bound variable then ()
               else rejected "Bind variable is malformed or already bound";
               Option.app (fn alternative =>
                 validate_plan alternative bound) fallback;
               validate_plan next (variable :: bound))
          | Refute_Eval.Split (tm, branches) =>
              let
                val _ = require_bound "Split scrutinee" bound [tm]
                val _ = validate_executable "Split scrutinee" [] [tm]
                fun branch (_, variables, next) =
                  if List.all (fresh_in bound) variables andalso
                     length (Util.distinct_terms variables) = length variables
                  then validate_plan next (variables @ bound)
                  else rejected "Split branch variable is already bound"
              in
                List.app branch branches
              end
          | Refute_Eval.Guard (tm, next) =>
              (require_bound "Guard" bound [tm];
               require_boolean "Guard" tm;
               validate_executable "Guard" [] [tm];
               validate_plan next bound)
          | Refute_Eval.NegGuard (tm, next) =>
              (require_bound "Neg Guard" bound [tm];
               require_boolean "Neg Guard" tm;
               validate_executable "Neg Guard" [] [tm];
               validate_plan next bound)
          | Refute_Eval.SmartGuard {predicate, version, cont} =>
              let
                val (program, ins) =
                  case smart_guard_lookup
                      {relation = predicate, version = version} programs of
                      SOME found => found
                    | NONE => rejected
                        "stale or non-all-input smart Guard"
              in
                require_bound "smart Guard" bound [predicate];
                require_bound "smart Guard input" bound ins;
                validate_executable "smart Guard"
                  [#relation program] [predicate];
                validate_plan cont bound
              end
          | Refute_Eval.Enum {rel, mode, version, ins, outs, cont} =>
              let
                val program as {relation = program_relation,
                                mode = program_mode,
                                version = program_version, ...} =
                  program_for rel mode
                val _ = if Refute_SmartGen.same_relation rel program_relation
                    andalso Refute_SmartGen.eq_mode (mode, program_mode)
                    andalso Refute_SmartGen.same_program_version
                      (version, program_version)
                  then () else rejected "stale enumerator cache key/version"
                val (expected_ins, expected_outs) =
                  mode_shape_with rejected rel mode
                val _ = if same_types (map Term.type_of ins) expected_ins
                    andalso same_types (map Term.type_of outs) expected_outs
                  then () else rejected "Enum mode/arity/types mismatch"
                val _ = require_bound "Enum input" bound ins
                val _ = validate_executable "Enum input" [] ins
                val extended =
                  validate_patterns "Enum output" bound outs
              in
                validate_plan cont extended
              end
          | Refute_Eval.Prune => ()
      val _ = List.app (fn plan => validate_plan plan []) plans
    in
      ()
    end

  fun prepare strategy plans =
    let
      val entries = Refute_SmartGen.enumerator_snapshot ()

      fun lookup relation mode =
        Option.map #program
          (find_by_mode #program relation mode entries)

      fun top_program relation mode version =
        case lookup relation mode of
            SOME program =>
              if Refute_SmartGen.same_program_version
                   (version, #version program)
              then program else reject "stale Enum version"
          | NONE => reject "missing top-level enumerator program"

      fun guard_program predicate version =
        case smart_guard_lookup
            {relation = predicate, version = version}
            (map #program entries) of
            SOME (found, _) => found
          | NONE => reject "stale or non-all-input smart Guard"

      val collect = collect_programs reject lookup top_program guard_program

      val programs = List.foldl (fn (plan, result) => collect plan result)
        [] plans
      val _ = if null programs orelse strategy = Refute_Eval.Exhaustive
        then ()
        else reject "smart generators currently require exhaustive testing"

      val _ = validate reject programs plans
    in
      programs
    end

  fun generator_types programs =
    List.foldl (fn (ty, result) =>
      if Util.member_type ty result then result else result @ [ty])
      [] (List.concat (map Refute_SmartGen.enumerator_gen_types programs))

  fun tuple_type [] = Type.bool
    | tuple_type tys = pairSyntax.list_mk_prod tys

  fun pack_terms [] = boolSyntax.T
    | pack_terms terms = pairSyntax.list_mk_pair terms

  fun unpack_terms [] _ = []
    | unpack_terms [_] tm = [tm]
    | unpack_terms (_ :: tys) tm =
        pairSyntax.mk_fst tm :: unpack_terms tys (pairSyntax.mk_snd tm)

  fun substitute env tm = Term.subst (map (op |->) env) tm

  (* Compile [patterns] against [values] into a nest of case terms and
     equality tests, calling [success] with [environment] extended by the
     bindings the match introduced, and yielding [failure] wherever the
     match cannot succeed.  Both HOL-term substrates share this; they differ
     only in how [fresh] names the variables a constructor branch binds. *)
  fun match_patterns fresh patterns values environment failure success =
    let
      fun match_one pattern value additions continue =
        let
          val bound = additions @ environment
        in
          if Term.is_var pattern then
            (case List.find (fn (old, _) => Term.aconv old pattern) bound of
                 SOME (_, old_value) =>
                   boolSyntax.mk_cond
                     (boolSyntax.mk_eq (old_value, value),
                      continue additions, failure)
               | NONE => continue (additions @ [(pattern, value)]))
          else if special_literal pattern then
            boolSyntax.mk_cond
              (boolSyntax.mk_eq (pattern, value),
               continue additions, failure)
          else
            case Refute_Eval.fully_applied_constructor pattern of
                SOME (wanted, pattern_args) =>
                  let
                    val ty = Term.type_of value
                    val constructors = map (TypeBasePure.cinst ty)
                      (TypeBase.constructors_of ty)
                    fun branch constructor =
                      let
                        val (argument_types, _) =
                          boolSyntax.strip_fun (Term.type_of constructor)
                        val arguments = map fresh argument_types
                        val body =
                          if Term.same_const constructor wanted andalso
                             length arguments = length pattern_args then
                            match_many pattern_args arguments additions
                              continue
                          else failure
                      in
                        (Term.list_mk_comb (constructor, arguments), body)
                      end
                  in
                    TypeBase.mk_case (value, map branch constructors)
                  end
              | NONE =>
                  boolSyntax.mk_cond
                    (boolSyntax.mk_eq (substitute bound pattern, value),
                     continue additions, failure)
        end
      and match_many [] [] additions continue = continue additions
        | match_many (pattern :: patterns) (value :: values)
              additions continue =
            match_one pattern value additions (fn extended =>
              match_many patterns values extended continue)
        | match_many _ _ _ _ = failure
    in
      match_many patterns values [] (fn additions =>
        success (additions @ environment))
    end

  (* Lives here, not in [Refute_SmartGen]: [Refute_Eval.sig] takes
     [mode]/[program_version] FROM [Refute_SmartGen], so [Refute_SmartGen]
     sits below [Refute_Eval], and this function needs [match_patterns],
     which needs [Refute_Eval.fully_applied_constructor] from this module.
     Moving it to [Refute_SmartGen] would invert that dependency.  Its
     caller, [Refute_QC.negative_candidates], reaches across from above
     with a direct [Refute_EvalEnum.negation_condition] qualified
     reference -- a normal downward call, not a layering violation. *)

  (* The closed boolean condition "every clause of [program] fails
     against [values]" -- the complement of a fully-input relation at
     a mode [Refute_SmartGen.complement_available] admits.  Every
     clause's premises are [CpsGuard] only: a [Prem] premise would
     have blocked admission, and an admitted mode never needs a
     [Generator], so no fuel or recursion is needed and pattern
     mismatch or a guard testing false are the only ways a clause can
     fail.  The caller must still read the result with the same
     three-valued discipline as an ordinary guard: a stuck evaluation
     is not a decided [false], so it must never license the
     disjunction's negation. *)
  fun negation_condition
        ({clauses, ...} : Refute_SmartGen.enumerator) values =
    let
      (* [Refute_SmartGen.complement_available] admits only a mode with
         no output position and no [Prem] premise, so every clause here
         is expected to have empty [outs] and [CpsGuard]-only premises.
         Both are enforced two modules away, not here: guess instead of
         checking would silently test the wrong condition, so a
         violation is fatal rather than reported as unavailable. *)
      val serial = ref 0
      fun fresh ty =
        let val index = !serial
            val _ = serial := index + 1
        in Term.mk_var ("negguard_pat_" ^ Int.toString index, ty) end
      fun guard_term (Refute_SmartGen.CpsGuard tm) = tm
        | guard_term _ = reject
            "negation_condition: clause premise is not a guard"
      fun holds (Refute_SmartGen.CpsClause {ins, premises, outs}) =
        (if null outs then ()
         else reject "negation_condition: clause binds an output position";
         match_patterns fresh ins values [] boolSyntax.F (fn environment =>
           case map (substitute environment o guard_term) premises of
               [] => boolSyntax.T
             | guards => boolSyntax.list_mk_conj guards))
    in
      case clauses of
          [] => boolSyntax.T
        | _ => boolSyntax.mk_neg (boolSyntax.list_mk_disj (map holds clauses))
    end

  fun conjunction [] = raise Fail "Refute enum empty definition"
    | conjunction equations = boolSyntax.list_mk_conj equations

  type hol_enumerator =
    {program : Refute_SmartGen.enumerator, function : term,
     input_types : hol_type list, output_types : hol_type list}

  type definition =
    {theorem : Thm.thm, enumerators : hol_enumerator list,
     generator_types : hol_type list}

  fun define {prefix, programs, after_define} =
    if null programs then
      {theorem = boolTheory.TRUTH, enumerators = [], generator_types = []}
    else
      let
        val gen_types = generator_types programs
        fun named suffix ty = Term.mk_var (prefix ^ suffix, ty)
        fun skeleton (index, program as {relation, mode, ...} :
              Refute_SmartGen.enumerator) =
          let
            val (input_types, output_types) = mode_shape relation mode
            val domains = map listSyntax.mk_list_type gen_types @
              input_types @ [numSyntax.num]
            val function = named ("enum_" ^ Int.toString index)
              (boolSyntax.list_mk_fun
                (domains, listSyntax.mk_list_type
                  (tuple_type output_types)))
          in
            {program = program, function = function,
             input_types = input_types, output_types = output_types}
          end
        val skeletons = Lib.mapi (fn index => fn program =>
          skeleton (index, program)) programs
        fun lookup relation mode =
          case find_by_mode #program relation mode skeletons of
              SOME found => found
            | NONE => reject "enumerator dependency is absent"
        val gen_formals = Lib.mapi (fn index => fn ty =>
          named ("enum_values_" ^ Int.toString index)
            (listSyntax.mk_list_type ty)) gen_types
        fun generator_values ty =
          case List.find (fn (other, _) => Util.same_type other ty)
              (ListPair.zip (gen_types, gen_formals)) of
              SOME (_, values) => values
            | NONE => reject "generator dependency is absent"
        fun call {function, ...} inputs fuel =
          Term.list_mk_comb (function, gen_formals @ inputs @ [fuel])
        fun bind values variable body = listSyntax.mk_flat
          (listSyntax.mk_map (Term.mk_abs (variable, body), values))

        val match_serial = ref 0
        fun fresh ty =
          let val index = !match_serial
              val _ = match_serial := index + 1
          in named ("enum_match_" ^ Int.toString index) ty end

        val match = match_patterns fresh

        fun equations data =
          let
            val {program = {clauses, ...}, input_types,
                 output_types, ...} = data
            val formals = Lib.mapi (fn index => fn ty =>
              named ("enum_in_" ^ Int.toString index) ty) input_types
            val fuel = named "enum_fuel" numSyntax.num
            val output_ty = tuple_type output_types
            val empty = listSyntax.mk_list ([], output_ty)
            fun premises outs [] env =
                  listSyntax.mk_list
                    ([pack_terms (map (substitute env) outs)], output_ty)
              | premises outs (premise :: rest) env =
                  (case premise of
                       Refute_SmartGen.CpsGuard tm =>
                         boolSyntax.mk_cond
                           (substitute env tm,
                            premises outs rest env, empty)
                     | Refute_SmartGen.CpsGenerate variable =>
                         bind (generator_values (Term.type_of variable))
                           variable (premises outs rest
                             ((variable, variable) :: env))
                     | Refute_SmartGen.CpsCall
                         {rel, mode, ins, outs = patterns} =>
                         let
                           val dependency = lookup rel mode
                           val values = call dependency
                             (map (substitute env) ins) fuel
                           val result = fresh
                             (tuple_type (#output_types dependency))
                           val components = unpack_terms
                             (#output_types dependency) result
                           val body = match patterns components env empty
                             (premises outs rest)
                         in
                           bind values result body
                         end)
            fun clause (Refute_SmartGen.CpsClause
                  {ins, premises = steps, outs}) =
              match ins formals [] empty (premises outs steps)
            fun append [] = empty
              | append [tm] = tm
              | append (tm :: rest) =
                  listSyntax.mk_append (tm, append rest)
            val zero_lhs = call data formals (numSyntax.term_of_int 0)
            val suc_lhs = call data formals (numSyntax.mk_suc fuel)
          in
            [boolSyntax.mk_eq (zero_lhs, empty),
             boolSyntax.mk_eq
               (suc_lhs, append (map clause clauses))]
          end
        val theorem = TotalDefn.Define
          [HOLPP.ANTIQUOTE
            (conjunction (List.concat (map equations skeletons)))]
        val _ = after_define theorem
        val _ = Option.app (fn hook => hook theorem)
          (!post_definition_failure_hook)
        fun defined variable = Term.prim_mk_const
          {Thy = Theory.current_theory (), Name = #1 (Term.dest_var variable)}
        val enumerators = map (fn
          {program, function, input_types, output_types} =>
          {program = program, function = defined function,
           input_types = input_types, output_types = output_types}) skeletons
      in
        {theorem = theorem, enumerators = enumerators,
         generator_types = gen_types}
      end

  fun enumerator_for enumerators relation mode =
    case find_by_mode
        (fn (item : hol_enumerator) => #program item)
        relation mode enumerators of
        SOME found => found
      | NONE => reject "enumerator dependency is absent"

  fun application ({function, ...} : hol_enumerator)
      generator_values inputs fuel =
    Term.list_mk_comb (function,
      generator_values @ inputs @ [numSyntax.term_of_int fuel])

  (* Shared process-global theory bracket.  Compute definitions and cv
     translations must serialize against one another.

     An ownerless binary lock rather than a [Mutex.mutex]: the bracket is
     released by whichever thread runs the substrate's [close], and
     [Refute_QC.bounded_close] runs a cleanup on a thread of its own, so
     the releasing thread is not in general the one that took the lock.
     Poly/ML leaves [Mutex.unlock] undefined in that case. *)
  val theory_lock = Synchronized.var "Refute evaluator theory" false

  fun try_lock_theory () =
    Synchronized.change_result theory_lock
      (fn held => (not held, true))

  fun unlock_theory () = Synchronized.change theory_lock (fn _ => false)

  (* Lock acquisition itself must admit timeout interrupts.  Once the lock
     is taken, interrupts remain masked until the caller has installed its
     cleanup state, so no lock can be leaked in that small transition. *)
  fun lock_interruptibly restore =
    let
      fun acquire () =
        if try_lock_theory () then ()
        else
          (restore (fn () => OS.Process.sleep (Time.fromReal 0.01)) ();
           acquire ())
    in
      acquire ()
    end

  (* Prefix allocation is independent of the theory bracket: cv allocates
     local names while holding [theory_lock], whereas compute allocates its
     definition prefix before the first run. *)
  val name_mutex = Mutex.mutex ()
  val name_serial = ref 0

  fun fresh_prefix stem =
    Multithreading.synchronized "Refute evaluator names" name_mutex
      (fn () =>
        let
          val serial = !name_serial
          val _ = name_serial := serial + 1
        in
          stem ^ Int.toString serial ^ "_"
        end)

  fun type_names () = List.map #1 (Theory.types "-")
  fun constant_names () =
    List.map (fn tm => #1 (Term.dest_const tm)) (Theory.constants "-")
  fun binding_names () = List.map (fn ((_, name), _) => name) (DB.thy "-")

  type snapshot =
    {theory : string, types : string list, constants : string list,
     bindings : string list}

  fun snapshot () : snapshot =
    {theory = Theory.current_theory (), types = type_names (),
     constants = constant_names (), bindings = binding_names ()}

  fun revert (baseline : snapshot) =
    let
      val after = snapshot ()
      val _ = if #theory baseline = #theory after then ()
        else raise Fail "Refute evaluator changed the current theory"
      fun additions current base =
        let val known = Redblackset.addList
          (Redblackset.empty String.compare, base)
        in List.filter (fn name =>
          not (Redblackset.member (known, name))) current end
      (* Cleanup must be best-effort: one stale or hook-rejected artifact
         must not prevent retirement of the rest of this private bracket. *)
      val first_error = ref NONE
      fun attempt action =
        case Exn.capture action () of
            Exn.Res _ => ()
          | Exn.Exn error =>
              if Option.isSome (!first_error) then ()
              else first_error := SOME error
      fun delete deletion names = List.app (fn name =>
        attempt (fn () => deletion name)) names
      val _ = delete Theory.delete_binding
        (additions (#bindings after) (#bindings baseline))
      val _ = delete Theory.delete_const
        (additions (#constants after) (#constants baseline))
      val _ = delete Theory.delete_type
        (additions (#types after) (#types baseline))
      val _ = attempt Theory.scrub
      val _ = attempt cv_memLib.prune_stale_entries
    in
      case !first_error of
          NONE => ()
        | SOME error => raise error
    end

  type theory_bracket =
    {baseline : snapshot, old_verbosity : cv_memLib.verbosity}

  fun open_theory_bracket () : theory_bracket =
    let
      val baseline = snapshot ()
      val old_verbosity = !cv_memLib.verbosity_level
      val _ = cv_memLib.verbosity_level := cv_memLib.Silent
    in
      {baseline = baseline, old_verbosity = old_verbosity}
    end

  fun close_theory_bracket
        ({baseline, old_verbosity} : theory_bracket) =
    let
      val result = Exn.capture revert baseline
      val _ = cv_memLib.verbosity_level := old_verbosity
    in
      case result of
          Exn.Res _ => ()
        | Exn.Exn error => raise CleanupFailed error
    end

  (* A compiled test holds its bracket from the first definition it makes
     until [close], and lifetimes legitimately overlap: the cv substrate
     opens its bracket while compiling (translation failures must surface
     as inapplicability, not as an evaluation result), so a compute test
     compiled from the same goal opens its own bracket, on the same
     thread, before the cv test is closed.  With a plain mutex that
     second open waits for a lock the caller itself holds and never
     returns.  Entry is therefore re-entrant for the holding thread:
     nested brackets share the outer baseline and only the outermost
     close reverts, so the theory is clean again exactly when no bracket
     is open.  Other threads still wait, because HOL's theory state
     tolerates only one mutator at a time. *)
  val bracket_owner = ref (NONE : Thread.thread option)
  val bracket_depth = ref 0
  val bracket_open = ref (NONE : theory_bracket option)

  fun holds_theory_bracket () =
    case !bracket_owner of
        NONE => false
      | SOME owner => Thread.equal (owner, Thread.self ())

  (* Both of these must be called with interrupts masked, so that a lock
     is never acquired or released without its bookkeeping. *)
  fun enter_theory_bracket restore_attributes =
    if holds_theory_bracket () then
      bracket_depth := !bracket_depth + 1
    else
      let
        val _ = lock_interruptibly restore_attributes
        (* Everything defined from here until the revert has finished is
           the evaluator's own, so it must not retire the enumerator
           programs the plan being compiled refers to. *)
        val _ = Refute_SmartGen.enter_private_theory ()
      in
        case Exn.capture open_theory_bracket () of
            Exn.Exn error =>
              (Refute_SmartGen.leave_private_theory ();
               unlock_theory (); raise error)
          | Exn.Res bracket =>
              (bracket_open := SOME bracket;
               bracket_owner := SOME (Thread.self ());
               bracket_depth := 1)
      end

  (* Returns the outermost close's cleanup outcome for the caller to
     release once it has decided which exception wins. *)
  fun leave_theory_bracket () =
    if !bracket_depth > 1 then
      (bracket_depth := !bracket_depth - 1; Exn.Res ())
    else
      let
        val bracket = !bracket_open
        val _ = bracket_open := NONE
        val _ = bracket_depth := 0
        val _ = bracket_owner := NONE
        val cleanup =
          case bracket of
              NONE => Exn.Res ()
            | SOME bracket => Exn.capture close_theory_bracket bracket
        (* After the revert, not before: the deletions it performs are
           themselves theory deltas of the evaluator's own making. *)
        val _ = Refute_SmartGen.leave_private_theory ()
        val _ = unlock_theory ()
      in
        cleanup
      end

  datatype 'a held_state =
      HeldIdle
    | HeldOpen
    | HeldReady of 'a

  datatype 'a held_bracket = HeldBracket of
    {state : 'a held_state ref, teardown : unit -> unit}

  fun held_bracket teardown =
    HeldBracket {state = ref HeldIdle, teardown = teardown}

  fun close_held_bracket (HeldBracket {state, teardown}) =
    case !state of
        HeldIdle => ()
      | _ =>
          Thread_Attributes.uninterruptible
            (fn _ => fn () =>
              let
                val cleanup = leave_theory_bracket ()
                val extra_cleanup = Exn.capture teardown ()
                val _ = state := HeldIdle
                val _ = Exn.release cleanup
              in
                Exn.release extra_cleanup
              end) ()

  fun start_held_bracket
        (held as HeldBracket {state, ...}) build =
    case !state of
        HeldReady value => value
      | HeldOpen =>
          raise Fail "Refute_EvalEnum.start_held_bracket: incomplete start"
      | HeldIdle =>
          Thread_Attributes.uninterruptible
            (fn restore_attributes => fn () =>
              let
                val _ = enter_theory_bracket restore_attributes
                val _ = state := HeldOpen
                (* [enter_theory_bracket] already fixes
                   [restore_attributes] at unit, so the built value leaves
                   the masked region through a slot rather than as the
                   restored call's result. *)
                val slot = ref NONE
                val result = Exn.capture
                  (restore_attributes
                    (fn () => slot := SOME (build ()))) ()
              in
                case (result, !slot) of
                    (Exn.Res _, SOME value) =>
                      (state := HeldReady value; value)
                  | (Exn.Exn error, _) =>
                      (close_held_bracket held; raise error)
                  | (Exn.Res _, NONE) =>
                      (close_held_bracket held;
                       raise Fail "Refute_EvalEnum.\
                         \start_held_bracket: no value")
              end) ()

  fun with_clean_theory body =
    Thread_Attributes.uninterruptible
      (fn restore_attributes => fn () =>
        let
          val _ = enter_theory_bracket restore_attributes
          (* As in [start_held_bracket]: one restore type per
             [uninterruptible] call, so the body's value comes back
             through a slot. *)
          val slot = ref NONE
          val result = Exn.capture
            (restore_attributes (fn () => slot := SOME (body ()))) ()
          val cleanup = leave_theory_bracket ()
        in
          case (result, !slot) of
              (Exn.Exn error, _) => raise error
            | (Exn.Res _, SOME value) =>
                (Exn.release cleanup; value)
            | (Exn.Res _, NONE) =>
                (Exn.release cleanup;
                 raise Fail
                   "Refute_EvalEnum.with_clean_theory: no value")
        end) ()
end
