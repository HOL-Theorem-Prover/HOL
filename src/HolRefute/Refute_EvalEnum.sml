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

  fun mode_shape relation mode =
    let
      val _ = if Term.is_const relation then ()
        else reject "enumerator relation is not a constant"
      val (domains, range) = boolSyntax.strip_fun (Term.type_of relation)
      val modes = Refute_SmartGen.strip_mode mode
      val _ = if Util.same_type range Type.bool then ()
        else reject "enumerator relation does not return bool"
      val _ = if length domains = length modes andalso
          List.all Refute_SmartGen.first_order_mode modes then ()
        else reject "enumerator mode/arity mismatch"
      val arguments = Lib.mapi (fn index => fn ty =>
        Term.mk_var ("refute_enum_shape_" ^ Int.toString index, ty)) domains
      val (ins, outs) = Refute_SmartGen.split_arguments mode arguments
    in
      (map Term.type_of ins, map Term.type_of outs)
    end
    handle Feedback.HOL_ERR _ => reject "enumerator mode/type mismatch"

  fun same_types left right =
    length left = length right andalso
    ListPair.allEq (fn (first, second) =>
      Util.same_type first second) (left, right)

  fun special_literal tm =
    Literal.is_numeral tm orelse intSyntax.is_int_literal tm orelse
    Literal.is_char_lit tm orelse Literal.is_string_lit tm orelse
    oneSyntax.is_one tm orelse wordsSyntax.is_word_literal tm orelse
    Term.aconv tm boolSyntax.T orelse Term.aconv tm boolSyntax.F

  fun prepare strategy plans =
    let
      val entries = Refute_SmartGen.enumerator_snapshot ()

      fun lookup relation mode =
        Option.map #program (List.find (fn {program = {relation = other,
            mode = other_mode, ...}, ...} =>
          Refute_SmartGen.same_relation relation other andalso
          Refute_SmartGen.eq_mode (mode, other_mode)) entries)

      fun top_program relation mode version =
        case lookup relation mode of
            SOME program =>
              if Refute_SmartGen.same_program_version
                   (version, #version program)
              then program else reject "stale Enum version"
          | NONE => reject "missing top-level enumerator program"

      fun add program programs =
        if List.exists (same_program program) programs then programs
        else programs @ [program]

      fun closure program programs =
        if List.exists (same_program program) programs then programs
        else
          let
            val programs = add program programs
            fun calls (Refute_SmartGen.CpsClause {premises, ...}) =
              List.mapPartial (fn Refute_SmartGen.CpsCall
                    {rel, mode, ...} =>
                    (case lookup rel mode of
                         SOME dependency => SOME dependency
                       | NONE => reject
                           "missing recursive enumerator dependency")
                | _ => NONE) premises
          in
            List.foldl (fn (dependency, result) =>
              closure dependency result) programs
              (List.concat (map calls (#clauses program)))
          end

      fun all_input predicate version programs =
        let
          val (relation, arguments) = HolKernel.strip_comb predicate
          fun suitable program =
            Refute_SmartGen.same_relation relation (#relation program) andalso
            Refute_SmartGen.same_program_version
              (version, #version program) andalso
            (case Refute_SmartGen.top_level_parts
                    (#mode program) arguments of
                 SOME (_, []) => true
               | _ => false)
          val program =
            case List.find suitable (map #program entries) of
                SOME found => found
              | NONE => reject "stale or non-all-input smart Guard"
        in
          closure program programs
        end
        handle Feedback.HOL_ERR _ =>
          reject "stale or non-all-input smart Guard"

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
          | Refute_Eval.SmartGuard {predicate, version, cont} =>
              collect cont (all_input predicate version programs)
          | Refute_Eval.Enum {rel, mode, version, cont, ...} =>
              collect cont (closure (top_program rel mode version) programs)
          | Refute_Eval.Prune => programs

      val programs = List.foldl (fn (plan, result) => collect plan result)
        [] plans
      val _ = if null programs orelse strategy = Refute_Eval.Exhaustive
        then ()
        else reject "smart generators currently require exhaustive testing"

      fun vars_bound bound tm =
        List.all (fn variable => List.exists (fn old =>
          Term.aconv old variable) bound) (Term.free_vars_lr tm)
      fun require_bound label bound terms =
        if List.all (vars_bound bound) terms then ()
        else reject (label ^ " uses an unbound variable")
      fun fresh_in bound variable =
        not (List.exists (fn old => Term.aconv old variable) bound)

      fun validate_executable label consumed terms =
        if null programs then ()
        else let
          val constants = Refute_Core.nonexecutable_constants terms
          val remaining = List.filter (fn constant =>
            not (List.exists (fn allowed =>
              Term.same_const allowed constant) consumed)) constants
          val has_binder = List.exists (fn tm =>
            not (null (HolKernel.find_terms Term.is_abs tm))) terms
        in
          if has_binder then
            reject (label ^ " contains an unexpanded binder")
          else if null remaining then ()
          else reject (label ^ " is nonexecutable: " ^
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
        else reject (label ^ " does not have type bool")

      fun program_for relation mode =
        case List.find (fn ({relation = other, mode = other_mode, ...} :
            Refute_SmartGen.enumerator) =>
          Refute_SmartGen.same_relation relation other andalso
          Refute_SmartGen.eq_mode (mode, other_mode)) programs of
            SOME program => program
          | NONE => reject "enumerator dependency is absent"

      fun validate_program
            ({relation, mode, clauses, ...} : Refute_SmartGen.enumerator) =
        let
          val (input_types, output_types) = mode_shape relation mode
          fun premise (item, current) =
            case item of
                Refute_SmartGen.CpsGenerate variable =>
                  if Term.is_var variable andalso fresh_in current variable
                  then current @ [variable]
                  else reject
                    "generator variable is malformed or already bound"
              | Refute_SmartGen.CpsGuard tm =>
                  (require_bound "enumerator Guard" current [tm];
                   require_boolean "enumerator Guard" tm;
                   validate_executable "enumerator Guard" [] [tm]; current)
              | Refute_SmartGen.CpsCall {rel, mode, ins, outs} =>
                  let
                    val _ = program_for rel mode
                    val (expected_ins, expected_outs) = mode_shape rel mode
                    val _ = if same_types (map Term.type_of ins) expected_ins
                        andalso same_types
                          (map Term.type_of outs) expected_outs then ()
                      else reject "recursive call mode/arity/types mismatch"
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
                then () else reject "clause mode/arity/types mismatch"
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
              else reject "Gen variable is malformed or already bound"
          | Refute_Eval.Bind (variable, tm, fallback, next) =>
              (require_bound "Bind expression" bound [tm];
               validate_executable "Bind expression" [] [tm];
               if Term.is_var variable andalso fresh_in bound variable then ()
               else reject "Bind variable is malformed or already bound";
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
                  else reject "Split branch variable is already bound"
              in
                List.app branch branches
              end
          | Refute_Eval.Guard (tm, next) =>
              (require_bound "Guard" bound [tm];
               require_boolean "Guard" tm;
               validate_executable "Guard" [] [tm];
               validate_plan next bound)
          | Refute_Eval.SmartGuard {predicate, version, cont} =>
              let
                val (relation, arguments) = HolKernel.strip_comb predicate
                fun suitable program =
                  if Refute_SmartGen.same_relation
                       relation (#relation program) andalso
                     Refute_SmartGen.same_program_version
                       (version, #version program) then
                    (case Refute_SmartGen.top_level_parts
                            (#mode program) arguments of
                         SOME (ins, []) => SOME ins
                       | _ => NONE)
                  else NONE
                val (program, ins) =
                  case List.mapPartial (fn program => Option.map
                    (fn ins => (program, ins)) (suitable program)) programs of
                      found :: _ => found
                    | [] => reject "stale or non-all-input smart Guard"
              in
                require_bound "smart Guard" bound [predicate];
                require_bound "smart Guard input" bound ins;
                validate_executable "smart Guard"
                  [#relation program] [predicate];
                validate_plan cont bound
              end
          | Refute_Eval.Enum {rel, mode, version, ins, outs, cont} =>
              let
                val program = program_for rel mode
                val _ = if Refute_SmartGen.same_program_version
                    (version, #version program) then ()
                  else reject "stale enumerator cache key/version"
                val (expected_ins, expected_outs) = mode_shape rel mode
                val _ = if same_types (map Term.type_of ins) expected_ins
                    andalso same_types (map Term.type_of outs) expected_outs
                  then () else reject "Enum mode/arity/types mismatch"
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
      programs
    end

  fun generator_types programs =
    List.foldl (fn (ty, result) =>
      if List.exists (Util.same_type ty) result then result else result @ [ty])
      [] (List.concat (map Refute_SmartGen.enumerator_gen_types programs))

  fun tuple_type [] = Type.bool
    | tuple_type [ty] = ty
    | tuple_type (ty :: tys) =
        pairSyntax.mk_prod (ty, tuple_type tys)

  fun pack_terms [] = boolSyntax.T
    | pack_terms [tm] = tm
    | pack_terms (tm :: terms) =
        pairSyntax.mk_pair (tm, pack_terms terms)

  fun unpack_terms [] _ = []
    | unpack_terms [_] tm = [tm]
    | unpack_terms (_ :: tys) tm =
        pairSyntax.mk_fst tm :: unpack_terms tys (pairSyntax.mk_snd tm)

  fun substitute env tm =
    Term.subst (map (fn (redex, residue) =>
      {redex = redex, residue = residue}) env) tm

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
          case List.find (fn {program = {relation = other,
              mode = other_mode, ...}, ...} =>
            Refute_SmartGen.same_relation relation other andalso
            Refute_SmartGen.eq_mode (mode, other_mode)) skeletons of
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

        fun match_one pattern value env additions failure success =
          if Term.is_var pattern then
            (case List.find (fn (old, _) => Term.aconv old pattern)
                    (additions @ env) of
                 SOME (_, old_value) =>
                   boolSyntax.mk_cond
                     (boolSyntax.mk_eq (old_value, value),
                      success env additions, failure)
               | NONE => success env (additions @ [(pattern, value)]))
          else if special_literal pattern then
            boolSyntax.mk_cond
              (boolSyntax.mk_eq (pattern, value),
               success env additions, failure)
          else
            case Refute_Eval.fully_applied_constructor pattern of
                SOME (wanted, pattern_args) =>
                  let
                    val ty = Term.type_of value
                    val constructors = TypeBase.constructors_of ty
                    val raw_case = TypeBase.case_const_of ty
                    val raw_ty = hd (#1 (boolSyntax.strip_fun
                      (Term.type_of raw_case)))
                    val case_constant = Term.inst
                      (Type.match_type raw_ty ty) raw_case
                    val (case_domains, _) = boolSyntax.strip_fun
                      (Term.type_of case_constant)
                    val branch_types = List.take
                      (tl case_domains, length constructors)
                    fun branch (constructor, branch_ty) =
                      let
                        val (argument_types, _) = boolSyntax.strip_fun branch_ty
                        val arguments = map fresh argument_types
                        val body =
                          if Term.same_const constructor wanted andalso
                             length arguments = length pattern_args then
                            match_many pattern_args arguments env additions
                              failure success
                          else failure
                      in
                        Term.list_mk_abs (arguments, body)
                      end
                  in
                    HolKernel.list_mk_icomb case_constant
                      (value :: ListPair.mapEq branch
                        (constructors, branch_types))
                  end
              | NONE =>
                  boolSyntax.mk_cond
                    (boolSyntax.mk_eq
                      (substitute (additions @ env) pattern, value),
                     success env additions, failure)
        and match_many [] [] env additions _ success =
              success env additions
          | match_many (pattern :: patterns) (value :: values)
              env additions failure success =
              match_one pattern value env additions failure
                (fn next_env => fn next_additions =>
                  match_many patterns values next_env next_additions
                    failure success)
          | match_many _ _ _ _ failure _ = failure

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
                           val body = match_many patterns components env []
                             empty (fn old => fn additions =>
                               premises outs rest (additions @ old))
                         in
                           bind values result body
                         end)
            fun clause (Refute_SmartGen.CpsClause
                  {ins, premises = steps, outs}) =
              match_many ins formals [] [] empty
                (fn env => fn additions =>
                  premises outs steps (additions @ env))
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
    case List.find (fn ({program = {relation = other,
        mode = other_mode, ...}, ...} : hol_enumerator) =>
      Refute_SmartGen.same_relation relation other andalso
      Refute_SmartGen.eq_mode (mode, other_mode)) enumerators of
        SOME found => found
      | NONE => reject "enumerator dependency is absent"

  fun application ({function, ...} : hol_enumerator)
      generator_values inputs fuel =
    Term.list_mk_comb (function,
      generator_values @ inputs @ [numSyntax.term_of_int fuel])

  fun has_enum current =
    case current of
        Refute_Eval.Enum _ => true
      | Refute_Eval.SmartGuard _ => true
      | Refute_Eval.Gen (_, next) => has_enum next
      | Refute_Eval.Bind (_, _, fallback, next) =>
          has_enum next orelse Option.getOpt (Option.map has_enum fallback,
            false)
      | Refute_Eval.Split (_, branches) =>
          List.exists (has_enum o #3) branches
      | Refute_Eval.Guard (_, next) => has_enum next
      | _ => false

  (* Shared process-global theory bracket.  Compute definitions and cv
     translations must serialize against one another. *)
  val theory_mutex = Mutex.mutex ()

  (* Prefix allocation is independent of the theory bracket: cv allocates
     local names while holding [theory_mutex], whereas compute allocates its
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
    in
      List.app Theory.delete_type
        (additions (#types after) (#types baseline));
      List.app Theory.delete_const
        (additions (#constants after) (#constants baseline));
      List.app Theory.delete_binding
        (additions (#bindings after) (#bindings baseline));
      Theory.scrub ();
      cv_memLib.prune_stale_entries ()
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

  fun with_clean_theory body =
    Multithreading.synchronized "Refute evaluator theory" theory_mutex
      (fn () => Thread_Attributes.uninterruptible
        (fn restore_attributes => fn () =>
          let
            val bracket = open_theory_bracket ()
            val result = Exn.capture (restore_attributes body) ()
            val _ = close_theory_bracket bracket
          in
            Exn.release result
          end) ())
end
