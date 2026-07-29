open HolKernel Parse boolLib bossLib
open refuteTheory refute_cvTheory

structure Refute_EvalCv = struct
  type term = Term.term
  type hol_type = Type.hol_type
  structure Util = Refute_Util

  datatype 'a cv_attempt =
      CvSuccess of 'a
    | CvInapplicable of string list

  type generator =
    {ty : hol_type, exhaustive : term, random : term}

  exception Unsupported of string

  fun fresh_prefix () =
    Refute_EvalEnum.fresh_prefix "refute_cv_"

  type snapshot = Refute_EvalEnum.snapshot
  val snapshot = Refute_EvalEnum.snapshot
  val with_clean_theory = Refute_EvalEnum.with_clean_theory

  fun map_index function = Lib.mapi (fn index => fn value =>
    function (index, value))

  val rand_below_tm =
    Term.prim_mk_const {Thy = "refute", Name = "rand_below"}

  fun table_entry ty exhaustive random =
    (ty, {ty = ty, exhaustive = exhaustive, random = random})

  val generator_table =
    [table_entry ``:num``
       ``refute_cv$refute_cv_exh_num`` ``refute_cv$refute_cv_rnd_num``,
     table_entry ``:int``
       ``refute_cv$refute_cv_exh_int`` ``refute_cv$refute_cv_rnd_int``,
     table_entry ``:char``
       ``refute_cv$refute_cv_exh_char`` ``refute_cv$refute_cv_rnd_char``,
     table_entry ``:bool``
       ``refute_cv$refute_cv_exh_bool`` ``refute_cv$refute_cv_rnd_bool``,
     table_entry ``:refute$rf1``
       ``refute_cv$refute_cv_exh_rf1`` ``refute_cv$refute_cv_rnd_rf1``,
     table_entry ``:refute$rf2``
       ``refute_cv$refute_cv_exh_rf2`` ``refute_cv$refute_cv_rnd_rf2``,
     table_entry ``:refute$rf3``
       ``refute_cv$refute_cv_exh_rf3`` ``refute_cv$refute_cv_rnd_rf3``,
     table_entry ``:refute$rf4``
       ``refute_cv$refute_cv_exh_rf4`` ``refute_cv$refute_cv_rnd_rf4``,
     table_entry ``:refute$rf5``
       ``refute_cv$refute_cv_exh_rf5`` ``refute_cv$refute_cv_rnd_rf5``,
     table_entry ``:refute$rf6``
       ``refute_cv$refute_cv_exh_rf6`` ``refute_cv$refute_cv_rnd_rf6``,
     table_entry ``:word8``
       ``refute_cv$refute_cv_exh_word8`` ``refute_cv$refute_cv_rnd_word8``,
     table_entry ``:word16``
       ``refute_cv$refute_cv_exh_word16`` ``refute_cv$refute_cv_rnd_word16``,
     table_entry ``:word32``
       ``refute_cv$refute_cv_exh_word32`` ``refute_cv$refute_cv_rnd_word32``,
     table_entry ``:word64``
       ``refute_cv$refute_cv_exh_word64`` ``refute_cv$refute_cv_rnd_word64``,
     table_entry ``:num list``
       ``refute_cv$refute_cv_exh_num_list``
       ``refute_cv$refute_cv_rnd_num_list``,
     table_entry ``:num # num``
       ``refute_cv$refute_cv_exh_num_pair``
       ``refute_cv$refute_cv_rnd_num_pair``,
     table_entry ``:num option``
       ``refute_cv$refute_cv_exh_num_option``
       ``refute_cv$refute_cv_rnd_num_option``,
     table_entry ``:string``
       ``refute_cv$refute_cv_exh_string`` ``refute_cv$refute_cv_rnd_string``]

  fun table_generator ty =
    Option.map #2
      (List.find (fn (entry_ty, _) => Util.same_type entry_ty ty)
        generator_table)

  fun table_random_aux ty =
    if Util.same_type ty ``:num list`` then
      SOME ``refute_cv$refute_cv_rnd_num_list_aux``
    else if Util.same_type ty ``:string`` then
      SOME ``refute_cv$refute_cv_rnd_string_aux``
    else NONE

  fun registered ty entries =
    List.exists (fn (entry_ty, _) => Util.same_type entry_ty ty) entries

  datatype recipe =
      EnumRecipe of term list
    | DatatypeRecipe of
        {constrs : (term * hol_type list) list,
         recursive : bool list list, min_size : int list list,
         exhaustive_values : term list option}

  type template =
    {ty : hol_type, exhaustive_var : term,
     exhaustive_helpers : term list list,
     exhaustive_helper_equations : term list,
     random_aux_var : term, random_var : term,
     exhaustive_equations : term, random_aux_equations : term,
     random_equation : term}

  type bundle = template list

  (* Only name-independent equations and their quotations survive a call.
     Definitions, translations, and datatype encoders are always rebuilt. *)
  val template_cache : (hol_type, bundle) Redblackmap.dict ref =
    ref (Redblackmap.mkDict Type.compare)
  val cache_hits = ref 0
  val cache_misses = ref 0

  fun synthesis_stats () =
    {hits = !cache_hits, misses = !cache_misses}

  fun cv_type_name ty = Parse.type_to_string ty

  fun unsupported ty why =
    raise Unsupported (cv_type_name ty ^ " - " ^ why)

  fun check_in_fragment ty =
    if Type.is_vartype ty then unsupported ty "unresolved type variable"
    else if Refute_Gen.has_registered_generator ty then
      unsupported ty "custom or abstract generator registered"
    else ()

  fun recipe_of ty =
    (check_in_fragment ty;
      (case Refute_Gen.spec_of ty of
           Refute_Gen.GenEnum values => EnumRecipe values
         | Refute_Gen.GenDatatype
             {constrs, recursive, min_size, ...} =>
             DatatypeRecipe
               {constrs = constrs, recursive = recursive,
                min_size = min_size,
                exhaustive_values = Refute_Gen.enumerate ty}
         | Refute_Gen.GenFun _ =>
             unsupported ty "function type in data position"
         | Refute_Gen.GenCustom _ =>
             unsupported ty "custom generator registered"
         | Refute_Gen.GenNum _ =>
             unsupported ty "numeric type is outside the cv table")
      handle Refute_Gen.NoGenerator (_, why) => unsupported ty why)

  fun validate_supported root =
    let
      val seen = ref ([] : hol_type list)
      fun visit ty =
        if Util.member_type ty (!seen) then ()
        else
          let
            val _ = seen := ty :: !seen
            val _ = check_in_fragment ty
          in
            if Option.isSome (table_generator ty) then ()
            else
              case Refute_Gen.spec_of ty of
                  Refute_Gen.GenDatatype
                    {constrs, recursive, family, ...} =>
                    let
                      fun nested ((_, arguments), flags) =
                        List.exists (fn (argument, is_recursive) =>
                          is_recursive andalso
                          not (Util.member_type argument family))
                          (ListPair.zip (arguments, flags))
                      val _ =
                        if List.exists nested
                          (ListPair.zip (constrs, recursive)) then
                          unsupported ty
                            "nested recursive datatype generator"
                        else ()
                    in
                      List.app visit (List.concat (List.map #2 constrs))
                    end
                | Refute_Gen.GenFun _ =>
                    unsupported ty "function type in data position"
                | Refute_Gen.GenCustom _ =>
                    unsupported ty "custom generator registered"
                | Refute_Gen.GenNum _ => ()
                | Refute_Gen.GenEnum _ => ()
          end
          handle Refute_Gen.NoGenerator (_, why) => unsupported ty why
    in
      visit root
    end

  fun collect_recipes root =
    let
      val seen = ref ([] : (hol_type * recipe) list)

      fun visit ty =
        if Option.isSome (table_generator ty) orelse
           List.exists (fn (old_ty, _) => Util.same_type old_ty ty) (!seen)
        then ()
        else
          let
            val recipe = recipe_of ty
            val _ = seen := (ty, recipe) :: !seen
            val arguments =
              case recipe of
                  EnumRecipe _ => []
                | DatatypeRecipe {constrs, ...} =>
                    List.concat (List.map #2 constrs)
          in
            List.app visit arguments
          end
    in
      visit root;
      rev (!seen)
    end

  val function_type = boolSyntax.list_mk_fun

  fun placeholder index suffix ty =
    Term.mk_var
      ("refute_cv_template_" ^ Int.toString index ^ "_" ^ suffix, ty)

  fun numeral value = numSyntax.term_of_int value

  fun list_append [] element_ty = listSyntax.mk_list ([], element_ty)
    | list_append [values] _ = values
    | list_append (values :: rest) element_ty =
        listSyntax.mk_append (values, list_append rest element_ty)

  fun make_templates recipes =
    let
      fun variables (index, (ty, recipe)) =
        let
          val pair_ty = pairSyntax.mk_prod (ty, numSyntax.num)
          fun constructor_helpers (constructor_index, (_, args)) =
            List.map (fn argument_index =>
              let
                val prior = List.take (args, argument_index)
                val remaining = List.drop (args, argument_index)
                val domains = prior @
                  List.map listSyntax.mk_list_type remaining
              in
                placeholder index
                  ("exh_" ^ Int.toString constructor_index ^ "_" ^
                   Int.toString argument_index)
                  (function_type (domains, listSyntax.mk_list_type ty))
              end)
              (List.tabulate (length args, fn n => n))
          val helpers =
            case recipe of
                EnumRecipe _ => []
              | DatatypeRecipe
                  {constrs, exhaustive_values = NONE, ...} =>
                  List.map constructor_helpers
                    (ListPair.zip
                      (List.tabulate (length constrs, fn n => n), constrs))
              | DatatypeRecipe {exhaustive_values = SOME _, ...} => []
        in
          {ty = ty,
           exhaustive_var = placeholder index "exh"
             (function_type ([numSyntax.num],
                listSyntax.mk_list_type ty)),
           exhaustive_helpers = helpers,
           random_aux_var = placeholder index "rnd_aux"
             (function_type
                ([numSyntax.num, numSyntax.num, numSyntax.num], pair_ty)),
           random_var = placeholder index "rnd"
             (function_type ([numSyntax.num, numSyntax.num], pair_ty))}
        end

      val vars = map_index variables recipes

      fun find_vars ty =
        case List.find (fn data => Util.same_type (#ty data) ty) vars of
            SOME data => data
          | NONE => raise Fail "Refute cv template dependency missing"

      fun find_recipe ty =
        case List.find (fn (recipe_ty, _) => Util.same_type recipe_ty ty)
            recipes of
            SOME (_, recipe) => recipe
          | NONE => raise Fail "Refute cv recipe dependency missing"

      fun recipe_floor (EnumRecipe _) = 0
        | recipe_floor (DatatypeRecipe {min_size, ...}) =
            List.foldl Int.min 1073741823
              (List.map (fn row => List.foldl Int.max 0 row) min_size)

      fun minimum_term ty =
        case Refute_Gen.enumerate ty of
            SOME (value :: _) => value
          | _ =>
              (case table_generator ty of
                   SOME _ =>
                     (case Refute_Gen.spec_of ty of
                          Refute_Gen.GenNum kind =>
                            hd (Refute_EvalCompute.numeric_terms kind 0)
                        | _ =>
                            raise Fail "Refute cv table has no minimum")
                 | NONE =>
                     case find_recipe ty of
                         EnumRecipe (value :: _) => value
                       | EnumRecipe [] =>
                           raise Fail "Refute cv empty enumeration"
                       | DatatypeRecipe {constrs, min_size, ...} =>
                           let
                             fun row_floor row =
                               List.foldl Int.max 0 row
                             val entries = ListPair.zip (constrs, min_size)
                             val minimum = List.foldl (fn (entry, best) =>
                               if row_floor (#2 entry) < row_floor (#2 best)
                               then entry else best) (hd entries) (tl entries)
                             val (constructor, args) = #1 minimum
                           in
                             Term.list_mk_comb
                               (constructor, List.map minimum_term args)
                           end)

      fun functions ty =
        case table_generator ty of
            SOME {exhaustive, random, ...} =>
              {exhaustive = exhaustive, random = random,
               random_aux = table_random_aux ty}
          | NONE =>
              let val data = find_vars ty
              in
                {exhaustive = #exhaustive_var data,
                 random = #random_var data,
                 random_aux = SOME (#random_aux_var data)}
              end

      fun exhaustive_call ty size =
        let
          val function = #exhaustive (functions ty)
        in
          Term.mk_comb (function, size)
          handle Feedback.HOL_ERR error =>
            raise Unsupported
              ("generator call " ^
               Parse.type_to_string (Term.type_of function) ^
               " applied to " ^ Parse.type_to_string (Term.type_of size) ^
               ": " ^ Feedback.message_of error)
        end

      fun constructor_values constructor args helpers size =
        case (args, helpers) of
            ([], []) =>
              listSyntax.mk_list ([constructor], Term.type_of constructor)
          | (_, helper :: _) =>
              Term.list_mk_comb
                (helper, List.map (fn ty => exhaustive_call ty size) args)
          | _ => raise Fail "Refute cv malformed exhaustive helpers"

      fun helper_equations ty constructor args helpers =
        let
          fun equations (argument_index, helper) =
            let
              val prior_types = List.take (args, argument_index)
              val remaining_types = List.drop (args, argument_index)
              val current_ty = hd remaining_types
              val prior = map_index (fn (index, arg_ty) =>
                Term.mk_var
                  ("refute_cv_prior_" ^ Int.toString index, arg_ty))
                prior_types
              val current = Term.mk_var ("refute_cv_current", current_ty)
              val rest = Term.mk_var
                ("refute_cv_rest", listSyntax.mk_list_type current_ty)
              val later_types = tl remaining_types
              val later = map_index (fn (index, arg_ty) =>
                Term.mk_var
                  ("refute_cv_later_" ^ Int.toString index,
                   listSyntax.mk_list_type arg_ty)) later_types
              val empty = listSyntax.mk_list ([], current_ty)
              val result_empty = listSyntax.mk_list ([], ty)
              val nil_lhs = Term.list_mk_comb
                (helper, prior @ (empty :: later))
              val cons = listSyntax.mk_cons (current, rest)
              val cons_lhs = Term.list_mk_comb
                (helper, prior @ (cons :: later))
              val recurse = Term.list_mk_comb
                (helper, prior @ (rest :: later))
              val head_values = prior @ [current]
              val head_result =
                if argument_index + 1 = length args then
                  listSyntax.mk_list
                    ([Term.list_mk_comb (constructor, head_values)], ty)
                else
                  Term.list_mk_comb
                    (List.nth (helpers, argument_index + 1),
                     head_values @ later)
              val cons_rhs = listSyntax.mk_append (head_result, recurse)
            in
              [boolSyntax.mk_eq (nil_lhs, result_empty),
               boolSyntax.mk_eq (cons_lhs, cons_rhs)]
            end
        in
          List.concat (map_index equations helpers)
        end

      fun all_helper_equations ty recipe helper_rows =
        case recipe of
            EnumRecipe _ => []
          | DatatypeRecipe {exhaustive_values = SOME _, ...} => []
          | DatatypeRecipe {constrs, ...} =>
              List.concat
                (ListPair.mapEq (fn ((constructor, args), helpers) =>
                  helper_equations ty constructor args helpers)
                  (constrs, helper_rows))

      fun exhaustive_equations ty exhaustive helpers recipe =
        let
          val size = Term.mk_var ("size", numSyntax.num)
        in
          case recipe of
              EnumRecipe values =>
                boolSyntax.mk_eq
                  (Term.mk_comb (exhaustive, size),
                   listSyntax.mk_list (values, ty))
            | DatatypeRecipe {exhaustive_values = SOME values, ...} =>
                boolSyntax.mk_eq
                  (Term.mk_comb (exhaustive, size),
                   listSyntax.mk_list (values, ty))
            | DatatypeRecipe {constrs, ...} =>
                let
                  val n = Term.mk_var ("n", numSyntax.num)
                  val zero = numeral 0
                  val empty = listSyntax.mk_list ([], ty)
                  val zero_eq = boolSyntax.mk_eq
                    (Term.mk_comb (exhaustive, zero), empty)
                  val values = ListPair.mapEq
                    (fn ((constructor, args), constructor_helpers) =>
                      constructor_values constructor args
                        constructor_helpers n
                      handle Feedback.HOL_ERR error =>
                        raise Unsupported
                          ("constructor " ^ Parse.term_to_string constructor ^
                           " (" ^ Feedback.top_structure_of error ^ "." ^
                           Feedback.top_function_of error ^ "): " ^
                           Feedback.message_of error))
                    (constrs, helpers)
                  val suc_eq = boolSyntax.mk_eq
                    (Term.mk_comb (exhaustive, numSyntax.mk_suc n),
                     list_append values ty)
                in
                  boolSyntax.mk_conj (zero_eq, suc_eq)
                end
        end

      fun random_call ty recursive budget size state =
        let
          val {random, random_aux, ...} = functions ty
        in
          case random_aux of
              NONE =>
                if recursive then
                  raise Fail "Refute cv recursive table dependency"
                else Term.list_mk_comb (random, [size, state])
            | SOME aux =>
                let
                  val actual_budget =
                    if recursive then numSyntax.mk_minus (budget, numeral 1)
                    else numSyntax.mk_max
                      (numeral (Refute_Gen.own_floor
                        (Refute_Gen.spec_of ty)), budget)
                in
                  Term.list_mk_comb
                    (aux, [actual_budget, size, state])
                end
        end

      fun draw_arguments constructor args flags budget size state =
        let
          fun loop [] [] values current =
                pairSyntax.mk_pair
                  (Term.list_mk_comb (constructor, rev values), current)
            | loop (arg_ty :: more_args) (flag :: more_flags) values
                current =
                let
                  val index = length values
                  val value = Term.mk_var
                    ("refute_cv_value_" ^ Int.toString index, arg_ty)
                  val next = Term.mk_var
                    ("refute_cv_state_" ^ Int.toString index,
                     numSyntax.num)
                  val draw = random_call arg_ty flag budget size current
                  val body = loop more_args more_flags
                    (value :: values) next
                in
                  pairSyntax.mk_plet
                    (pairSyntax.mk_pair (value, next), draw, body)
                end
            | loop _ _ _ _ =
                raise Fail "Refute cv malformed constructor data"
        in
          loop args flags [] state
        end

      fun add_terms [] = numeral 0
        | add_terms [tm] = tm
        | add_terms (tm :: rest) =
            numSyntax.mk_plus (tm, add_terms rest)

      fun weight_term budget flags floors =
        if not (List.exists (fn flag => flag) flags) then numeral 1
        else if Term.aconv budget (numeral 0) then numeral 0
        else
          let
            fun depth (true, floor) = Int.max (0, floor - 1)
              | depth (false, _) = 0
            val minimum = List.foldl Int.max 0
              (ListPair.mapEq depth (flags, floors))
          in
            if minimum = 0 then budget
            else
              boolSyntax.mk_cond
                (numSyntax.mk_less (numeral minimum, budget),
                 budget, numeral 0)
          end

      fun choose draw entries =
        let
          fun build _ [(_, branch)] = branch
            | build total ((weight, branch) :: rest) =
                let
                  val next_total = numSyntax.mk_plus (total, weight)
                in
                  boolSyntax.mk_cond
                    (numSyntax.mk_less (draw, next_total), branch,
                     build next_total rest)
                end
            | build _ [] = raise Fail "Refute cv empty constructor list"
        in
          build (numeral 0) entries
        end

      fun datatype_random_body ty constrs recursive min_size budget size
          state =
        let
          fun entries [] [] [] = []
            | entries ((constructor, args) :: rest)
                (flags :: more_flags) (floors :: more_floors) =
                let
                  val weight = weight_term budget flags floors
                  val branch = draw_arguments constructor args flags budget
                    size (Term.mk_var ("state1", numSyntax.num))
                in
                  (weight, branch) ::
                    entries rest more_flags more_floors
                end
            | entries _ _ _ =
                raise Fail "Refute cv malformed datatype recipe"
          val all_entries = entries constrs recursive min_size
          val positive_entries =
            if Term.aconv budget (numeral 0) then
              List.filter (fn (weight, _) =>
                not (Term.aconv weight (numeral 0))) all_entries
            else all_entries
          val weights = List.map #1 positive_entries
          val draw = Term.mk_var ("choice", numSyntax.num)
          val state1 = Term.mk_var ("state1", numSyntax.num)
        in
          if null positive_entries then
            pairSyntax.mk_pair (minimum_term ty, state)
          else
            let
              val rand = Term.list_mk_comb
                (rand_below_tm, [add_terms weights, state])
              val selected = choose draw positive_entries
            in
              pairSyntax.mk_plet
                (pairSyntax.mk_pair (draw, state1), rand, selected)
            end
        end

      fun enum_random_body values state =
        let
          val draw = Term.mk_var ("choice", numSyntax.num)
          val state1 = Term.mk_var ("state1", numSyntax.num)
          val rand = Term.list_mk_comb
            (rand_below_tm, [numeral (length values), state])
          fun select _ [value] = value
            | select index (value :: rest) =
                boolSyntax.mk_cond
                  (boolSyntax.mk_eq (draw, numeral index), value,
                   select (index + 1) rest)
            | select _ [] = raise Fail "Refute cv empty enumeration"
          val result = pairSyntax.mk_pair (select 0 values, state1)
        in
          pairSyntax.mk_plet
            (pairSyntax.mk_pair (draw, state1), rand, result)
        end

      fun random_aux_equations ty aux recipe =
        let
          val budget = Term.mk_var ("budget", numSyntax.num)
          val size = Term.mk_var ("size", numSyntax.num)
          val state = Term.mk_var ("state", numSyntax.num)
          fun lhs actual_budget =
            Term.list_mk_comb (aux, [actual_budget, size, state])
        in
          case recipe of
              EnumRecipe values =>
                boolSyntax.mk_eq
                  (lhs budget, enum_random_body values state)
            | DatatypeRecipe {constrs, recursive, min_size, ...} =>
                let
                  val n = Term.mk_var ("n", numSyntax.num)
                  val zero = numeral 0
                  val zero_body = datatype_random_body ty constrs recursive
                    min_size zero size state
                  val suc = numSyntax.mk_suc n
                  val suc_body = datatype_random_body ty constrs recursive
                    min_size suc size state
                in
                  boolSyntax.mk_conj
                    (boolSyntax.mk_eq (lhs zero, zero_body),
                     boolSyntax.mk_eq (lhs suc, suc_body))
                end
        end

      fun random_equation ty random aux recipe =
        let
          val size = Term.mk_var ("size", numSyntax.num)
          val state = Term.mk_var ("state", numSyntax.num)
          val budget = numSyntax.mk_max (numeral (recipe_floor recipe), size)
        in
          boolSyntax.mk_eq
            (Term.list_mk_comb (random, [size, state]),
             Term.list_mk_comb (aux, [budget, size, state]))
        end

      fun stage label make =
        make ()
        handle Feedback.HOL_ERR error =>
          raise Unsupported
            (label ^ ": " ^ Feedback.message_of error)

      fun one ((ty, recipe), data) =
        let
          val exhaustive_helper_equations =
            stage "exhaustive helper template" (fn () =>
              all_helper_equations ty recipe
                (#exhaustive_helpers data))
          val exhaustive_equations = stage "exhaustive template" (fn () =>
            exhaustive_equations ty (#exhaustive_var data)
              (#exhaustive_helpers data) recipe)
          val random_aux_equations = stage "random auxiliary template"
            (fn () => random_aux_equations ty
              (#random_aux_var data) recipe)
          val random_equation = stage "random wrapper template" (fn () =>
            random_equation ty (#random_var data)
              (#random_aux_var data) recipe)
        in
          {ty = ty, exhaustive_var = #exhaustive_var data,
           exhaustive_helpers = #exhaustive_helpers data,
           exhaustive_helper_equations = exhaustive_helper_equations,
           random_aux_var = #random_aux_var data,
           random_var = #random_var data,
           exhaustive_equations = exhaustive_equations,
           random_aux_equations = random_aux_equations,
           random_equation = random_equation}
        end
    in
      ListPair.mapEq one (recipes, vars)
    end

  fun bundle_uptodate bundle =
    List.all (fn data =>
      Theory.uptodate_term (#exhaustive_equations data) andalso
      Theory.uptodate_term (#random_aux_equations data) andalso
      Theory.uptodate_term (#random_equation data) andalso
      List.all Theory.uptodate_term
        (#exhaustive_helper_equations data)) bundle

  fun template_bundle ty =
    let
      fun rebuild () =
        let
          val bundle = make_templates (collect_recipes ty)
          val _ = template_cache :=
            Redblackmap.insert (!template_cache, ty, bundle)
          val _ = cache_misses := !cache_misses + 1
        in
          bundle
        end
    in
      case Redblackmap.peek (!template_cache, ty) of
          SOME bundle =>
            if bundle_uptodate bundle then
              (cache_hits := !cache_hits + 1; bundle)
            else rebuild ()
        | NONE => rebuild ()
    end

  fun conjunction equations =
    case equations of
        [] => raise Fail "Refute cv empty definition bundle"
      | _ => boolSyntax.list_mk_conj equations

  val split_equations = boolSyntax.strip_conj

  fun instantiate_bundle prefix bundle =
    let
      fun fresh (index, data) =
        let
          fun variable suffix old =
            Term.mk_var
              (prefix ^ Int.toString index ^ "_" ^ suffix,
               Term.type_of old)
        in
          {ty = #ty data,
           exhaustive_var = variable "exh" (#exhaustive_var data),
           exhaustive_helpers =
             map_index (fn (constructor_index, row) =>
               map_index (fn (argument_index, old) =>
                 variable
                   ("exh_" ^ Int.toString constructor_index ^ "_" ^
                    Int.toString argument_index) old) row)
               (#exhaustive_helpers data),
           random_aux_var = variable "rnd_aux" (#random_aux_var data),
           random_var = variable "rnd" (#random_var data)}
        end
      val fresh_data = List.map fresh
        (ListPair.zip (List.tabulate (length bundle, fn n => n), bundle))
      fun helper_substitutions old fresh =
        List.concat
          (ListPair.mapEq (fn (old_row, fresh_row) =>
            ListPair.mapEq (fn (old_helper, fresh_helper) =>
              {redex = old_helper, residue = fresh_helper})
              (old_row, fresh_row))
            (#exhaustive_helpers old, #exhaustive_helpers fresh))
      val substitutions = List.concat
        (ListPair.mapEq (fn (old, fresh) =>
          [{redex = #exhaustive_var old,
            residue = #exhaustive_var fresh},
           {redex = #random_aux_var old,
            residue = #random_aux_var fresh},
           {redex = #random_var old, residue = #random_var fresh}] @
          helper_substitutions old fresh)
          (bundle, fresh_data))
      fun subst tm = Term.subst substitutions tm
      fun defined variable =
        Term.prim_mk_const
          {Thy = Theory.current_theory (),
           Name = #1 (Term.dest_var variable)}
      fun helper_triples (old, fresh) =
        let
          val old_helpers = List.concat (#exhaustive_helpers old)
          val fresh_helpers = List.concat (#exhaustive_helpers fresh)
          val equations = #exhaustive_helper_equations old
          fun one index =
            (List.nth (old_helpers, index),
             List.nth (fresh_helpers, index),
             [List.nth (equations, 2 * index),
              List.nth (equations, 2 * index + 1)])
        in
          List.tabulate (length old_helpers, one)
        end
      val triples = List.concat
        (ListPair.mapEq helper_triples (bundle, fresh_data))
      val defined_helpers = ref ([] : (term * term) list)
      fun define_helper (old, fresh, equations) =
        let
          val known = List.map (fn (old_helper, fresh_helper) =>
            {redex = old_helper, residue = defined fresh_helper})
            (!defined_helpers)
          val replacements =
            {redex = old, residue = fresh} :: known
          val instantiated = List.map
            (Term.subst replacements) equations
          val definition = TotalDefn.Define
            [HOLPP.ANTIQUOTE (conjunction instantiated)]
          val _ = defined_helpers := (old, fresh) :: !defined_helpers
        in
          definition
        end
      val helper_defs = List.map define_helper (rev triples)
      val main_substitutions = List.concat
        (ListPair.mapEq (fn (old, fresh) =>
          [{redex = #exhaustive_var old,
            residue = #exhaustive_var fresh}] @
          List.map (fn {redex, residue} =>
            {redex = redex, residue = defined residue})
            (helper_substitutions old fresh))
          (bundle, fresh_data))
      fun main_subst tm = Term.subst main_substitutions tm
      val exhaustive_def = TotalDefn.Define
        [HOLPP.ANTIQUOTE
          (conjunction (List.concat (List.map
             (split_equations o main_subst o #exhaustive_equations)
             bundle)))]
      val random_aux_def = TotalDefn.Define
        [HOLPP.ANTIQUOTE
          (conjunction (List.concat (List.map
             (split_equations o subst o #random_aux_equations)
             bundle)))]
      val wrapper_substitutions = List.concat
        (ListPair.mapEq (fn (old, fresh) =>
          [{redex = #random_aux_var old,
            residue = defined (#random_aux_var fresh)},
           {redex = #random_var old, residue = #random_var fresh}])
          (bundle, fresh_data))
      fun wrapper_subst tm = Term.subst wrapper_substitutions tm
      val random_def = TotalDefn.Define
        [HOLPP.ANTIQUOTE
          (conjunction (List.map
             (wrapper_subst o #random_equation) bundle))]
      val _ = List.app cv_transLib.cv_auto_trans helper_defs
      val _ = cv_transLib.cv_trans exhaustive_def
      val aux_variables = List.map #random_aux_var bundle
      fun rhs_mentions aux equation =
        List.exists (fn item =>
          Term.free_in aux (#2 (boolSyntax.dest_eq item)))
          (split_equations equation)
      val needs_precondition = List.exists (fn data =>
        List.exists (fn aux =>
          rhs_mentions aux (#random_aux_equations data)) aux_variables)
        bundle
      val _ =
        if not needs_precondition then
          cv_transLib.cv_auto_trans random_aux_def
        else
          let
            val first_aux = #random_aux_var (hd fresh_data)
            val pre_name = #1 (Term.dest_var first_aux) ^ "_pre"
            val pre_def =
              cv_transLib.cv_auto_trans_pre pre_name random_aux_def
            val pre_equations = CONJUNCTS pre_def

            fun prove_total (pre_equation, totals) =
              let
                val (_, pre_body) =
                  boolSyntax.strip_forall (Thm.concl pre_equation)
                val (pre_lhs, _) = boolSyntax.dest_eq pre_body
                val (pre_constant, _) = boolSyntax.strip_comb pre_lhs
                val budget = Term.mk_var ("budget", numSyntax.num)
                val size = Term.mk_var ("size", numSyntax.num)
                val state = Term.mk_var ("state", numSyntax.num)
                val pre_goal = boolSyntax.list_mk_forall
                  ([budget, size, state],
                   Term.list_mk_comb
                     (pre_constant, [budget, size, state]))
                (* cv_trans exposes the syntactic recursion guard as a
                   precondition.  Budget induction proves it total. *)
                val total = prove
                  (pre_goal,
                   Induct_on `budget` >>
                   rw (List.map Once (pre_def :: totals)))
                val _ = cv_memLib.cv_pre_add total
              in
                total :: totals
              end
            val _ = List.foldl prove_total [] (rev pre_equations)
          in
            ()
          end
      val _ = cv_transLib.cv_auto_trans random_def
      fun result data =
        {ty = #ty data, exhaustive = defined (#exhaustive_var data),
         random = defined (#random_var data)}
    in
      List.map result fresh_data
    end

  fun synthesise_generator ty =
    let
      val _ = validate_supported ty
    in
      case table_generator ty of
          SOME generator => generator
        | NONE =>
          let
            val generated = instantiate_bundle (fresh_prefix ())
              (template_bundle ty)
          in
            case List.find (fn data => Util.same_type (#ty data) ty)
                 generated of
                SOME result => result
              | NONE => raise Fail "Refute cv root generator missing"
          end
    end

  fun synthesise_generators types =
    List.map synthesise_generator types

  fun hol_error_reason error =
    let
      val origin =
        case Feedback.origins_of error of
            [] => "translation"
          | {origin_structure, origin_function, ...} :: _ =>
              if origin_function = "" then origin_structure
              else origin_structure ^ "." ^ origin_function
      val message = Feedback.message_of error
    in
      "cv: " ^ origin ^
      (if message = "" then "" else ": " ^ message)
    end

  (* Generated constants become stale on return.  The continuation form
     forces loop synthesis and evaluation to happen in-bracket. *)
  fun with_generators types continuation =
    (CvSuccess
       (with_clean_theory (fn () =>
          continuation (synthesise_generators types))))
    handle Unsupported reason => CvInapplicable ["cv: " ^ reason]
         | Feedback.HOL_ERR error =>
             CvInapplicable [hol_error_reason error]

  exception Precondition of string

  fun distinct_types types =
    rev (List.foldl (fn (ty, result) =>
      if Util.member_type ty result then result else ty :: result)
      [] types)

  fun plan_variables plan =
    let
      fun collect current variables =
        case current of
            Refute_Eval.Test _ => variables
          | Refute_Eval.Gen (variable, next) =>
              collect next (variable :: variables)
          | Refute_Eval.Bind (variable, _, fallback, next) =>
              collect next
                (case fallback of
                     NONE => variable :: variables
                   | SOME alternative =>
                       collect alternative (variable :: variables))
          | Refute_Eval.Split (_, branches) =>
              List.foldl (fn ((_, _, next), result) =>
                collect next result) variables branches
          | Refute_Eval.Guard (_, next) => collect next variables
          | Refute_Eval.SmartGuard {cont, ...} => collect cont variables
          | Refute_Eval.Enum {outs, cont, ...} =>
              collect cont
                (List.concat (map Term.free_vars_lr outs) @ variables)
          | Refute_Eval.Prune => variables
    in
      Util.distinct_terms (collect plan [])
    end

  fun plan_generator_types plan =
    distinct_types (Refute_Eval.plan_gen_types plan)

  fun plan_payloads plan =
    let
      fun collect current terms =
        case current of
            Refute_Eval.Test tm => tm :: terms
          | Refute_Eval.Gen (_, next) => collect next terms
          | Refute_Eval.Bind (_, tm, fallback, next) =>
              collect next
                (tm :: (case fallback of
                    NONE => terms
                  | SOME alternative => collect alternative terms))
          | Refute_Eval.Split (tm, branches) =>
              List.foldl (fn ((_, _, next), result) =>
                collect next result) (tm :: terms) branches
          | Refute_Eval.Guard (tm, next) => collect next (tm :: terms)
          | Refute_Eval.SmartGuard {predicate, cont, ...} =>
              collect cont (predicate :: terms)
          | Refute_Eval.Enum {ins, outs, cont, ...} =>
              collect cont (ins @ outs @ terms)
          | Refute_Eval.Prune => terms
    in
      collect plan []
    end

  val constants_in = HolKernel.find_terms Term.is_const

  val partial_names =
    [("list", "HD"), ("list", "TL"), ("list", "EL"), ("option", "THE"),
     ("sum", "OUTL"), ("sum", "OUTR"), ("list", "LAST"),
     ("list", "FRONT")]

  fun partial_constant plans =
    let
      val constants = List.concat
        (List.map (List.concat o List.map constants_in o plan_payloads)
          plans)
      fun is_partial tm =
        let val {Thy, Name, ...} = Term.dest_thy_const tm
        in List.exists (fn known => known = (Thy, Name)) partial_names end
    in
      Option.map (fn tm => #1 (Term.dest_const tm))
        (List.find is_partial constants)
    end

  fun env_type [] = Type.bool
    | env_type variables =
        pairSyntax.list_mk_prod (List.map Term.type_of variables)

  fun lookup_env variable env =
    case List.find (fn (old, _) => Term.aconv old variable) env of
        SOME (_, value) => value
      | NONE => raise Unsupported
          ("unbound result variable " ^ Parse.term_to_string variable)

  fun env_term [] _ = boolSyntax.T
    | env_term variables env =
        pairSyntax.list_mk_pair
          (List.map (fn variable => lookup_env variable env) variables)

  fun decode_env [] _ = []
    | decode_env [variable] value = [(variable, value)]
    | decode_env (variable :: rest) value =
        let val (head, tail) = pairSyntax.dest_pair value
        in (variable, head) :: decode_env rest tail end

  fun substitute env tm =
    Term.subst (List.map (fn (redex, residue) =>
      {redex = redex, residue = residue}) env) tm

  fun env_parameters env =
    Util.distinct_terms (List.map #2 (rev env))

  fun result_type variables =
    pairSyntax.mk_prod
      (numSyntax.num, optionSyntax.mk_option (env_type variables))

  fun no_hit variables counter =
    pairSyntax.mk_pair
      (counter, optionSyntax.mk_none (env_type variables))

  fun hit variables counter env =
    pairSyntax.mk_pair
      (counter, optionSyntax.mk_some (env_term variables env))

  fun named_variable name ty = Term.mk_var (name, ty)

  fun definition_head definition =
    let
      val equation = hd (CONJUNCTS definition)
      val (left, _) = boolSyntax.dest_eq (Thm.concl (SPEC_ALL equation))
    in
      #1 (boolSyntax.strip_comb left)
    end

  fun translate_checked prefix payloads definition =
    case cv_transLib.cv_auto_trans_opt_pre definition of
      NONE => ()
    | SOME _ =>
        raise Precondition
          (case partial_constant
             [List.foldr Refute_Eval.Guard Refute_Eval.Prune payloads] of
               SOME name => name
             | NONE => prefix)

  fun generator_for ty generators =
    case List.find (fn generator => Util.same_type (#ty generator) ty)
        generators of
        SOME generator => generator
      | NONE => raise Fail "Refute cv generator lookup failed"

  fun make_option_case option_tm none_body some_variable some_body =
    optionSyntax.mk_option_case
      (none_body, Term.mk_abs (some_variable, some_body), option_tm)

  fun make_split scrutinee branches env miss build =
    let
      val scrutinee' = substitute env scrutinee
      val ty = Term.type_of scrutinee'
      val constructors = TypeBase.constructors_of ty
      val raw_case_constant = TypeBase.case_const_of ty
      val raw_scrutinee_ty = hd (#1 (boolSyntax.strip_fun
        (Term.type_of raw_case_constant)))
      val case_constant = Term.inst
        (Type.match_type raw_scrutinee_ty ty) raw_case_constant
      val (case_domains, _) = boolSyntax.strip_fun
        (Term.type_of case_constant)
      val branch_types = List.take
        (tl case_domains, length constructors)
      fun branch_function (constructor, branch_ty) =
        let
          val stem = fresh_prefix ()
          val (argument_types, _) = boolSyntax.strip_fun branch_ty
          val arguments = map_index (fn (index, arg_ty) =>
            named_variable
              (stem ^ "case_" ^ Int.toString index) arg_ty)
            argument_types
          val matching = List.find (fn (expected, variables, _) =>
            Term.same_const expected constructor andalso
            length variables = length arguments) branches
          val body =
            case matching of
                NONE => miss
              | SOME (_, variables, next) =>
                  build next
                    (ListPair.zip (variables, arguments) @ env)
        in
          Term.list_mk_abs (arguments, body)
        end
      val functions = ListPair.mapEq branch_function
        (constructors, branch_types)
    in
      HolKernel.list_mk_icomb case_constant
        (scrutinee' :: functions)
    end

  val tuple_type = Refute_EvalEnum.tuple_type
  val unpack_terms = Refute_EvalEnum.unpack_terms

  fun define_enumerators prefix payloads programs =
    Refute_EvalEnum.define
      {prefix = prefix, programs = programs,
       after_define = translate_checked prefix payloads}

  val hol_enumerator_for = Refute_EvalEnum.enumerator_for

  (* The pattern compiler itself is shared with the enum substrate; only the
     naming of the variables a constructor branch binds is local. *)
  fun make_pattern_matches patterns values environment failure success =
    let
      val serial = ref 0
      fun fresh ty =
        let
          val index = !serial
          val _ = serial := index + 1
        in
          named_variable (fresh_prefix () ^ "pat_" ^ Int.toString index) ty
        end
    in
      Refute_EvalEnum.match_patterns fresh patterns values environment
        failure success
    end

  type loop_program =
    {variables : term list, result_ty : hol_type,
     application : int -> int -> term}

  fun define_exhaustive_search prefix payloads plan generators =
    let
      val variables = plan_variables plan
      val result_ty = result_type variables
      val size = named_variable (prefix ^ "size") numSyntax.num

      fun build current env skip =
        case current of
            Refute_Eval.Prune => no_hit variables skip
          | Refute_Eval.Test tm =>
              boolSyntax.mk_cond
                (substitute env tm, no_hit variables skip,
                 boolSyntax.mk_cond
                   (boolSyntax.mk_eq (skip, numeral 0),
                    hit variables (numeral 0) env,
                    no_hit variables
                      (numSyntax.mk_minus (skip, numeral 1))))
          | Refute_Eval.Guard (tm, next) =>
              boolSyntax.mk_cond
                (substitute env tm, build next env skip,
                 no_hit variables skip)
          | Refute_Eval.SmartGuard {predicate, cont, ...} =>
              boolSyntax.mk_cond
                (substitute env predicate, build cont env skip,
                 no_hit variables skip)
          | Refute_Eval.Enum _ =>
              raise Unsupported "Enum requires list compilation"
          | Refute_Eval.Bind (variable, tm, _, next) =>
              let
                val value = named_variable
                  (fresh_prefix () ^ "bound") (Term.type_of variable)
              in
                boolSyntax.mk_let
                  (Term.mk_abs
                    (value, build next ((variable, value) :: env) skip),
                   substitute env tm)
              end
          | Refute_Eval.Split (scrutinee, branches) =>
              make_split scrutinee branches env (no_hit variables skip)
                (fn next => fn branch_env =>
                  build next branch_env skip)
          | Refute_Eval.Gen (variable, next) =>
              let
                val stem = fresh_prefix ()
                val ty = Term.type_of variable
                val list_ty = listSyntax.mk_list_type ty
                val head = named_variable (stem ^ "head") ty
                val tail = named_variable (stem ^ "tail") list_ty
                val current_parameters = env_parameters env
                val helper_ty = function_type
                  (list_ty :: numSyntax.num ::
                   List.map Term.type_of current_parameters @
                   [numSyntax.num], result_type variables)
                val helper = named_variable (stem ^ "find") helper_ty
                fun helper_call list counter =
                  Term.list_mk_comb
                    (helper, list :: size ::
                     current_parameters @ [counter])
                val nil_lhs = helper_call
                  (listSyntax.mk_list ([], ty)) skip
                val nil_eq = boolSyntax.mk_eq
                  (nil_lhs, no_hit variables skip)
                val attempt = build next
                  ((variable, head) :: env) skip
                val remaining = named_variable
                  (stem ^ "remaining") numSyntax.num
                val found = named_variable
                  (stem ^ "found") (env_type variables)
                val recurse = helper_call tail remaining
                val return_found = pairSyntax.mk_pair
                  (remaining, optionSyntax.mk_some found)
                val answer = named_variable (stem ^ "answer")
                  (optionSyntax.mk_option (env_type variables))
                val after_attempt = pairSyntax.mk_plet
                  (pairSyntax.mk_pair (remaining, answer),
                   attempt,
                   make_option_case answer recurse found return_found)
                val cons_lhs = helper_call
                  (listSyntax.mk_cons (head, tail)) skip
                val definition = TotalDefn.Define
                  [HOLPP.ANTIQUOTE
                    (boolSyntax.mk_conj
                      (nil_eq,
                       boolSyntax.mk_eq (cons_lhs, after_attempt)))]
                val _ = translate_checked prefix payloads definition
                val helper_constant = definition_head definition
                val exhaustive = #exhaustive
                  (generator_for ty generators)
              in
                Term.list_mk_comb
                  (helper_constant,
                   Term.mk_comb (exhaustive, size) :: size ::
                   current_parameters @ [skip])
              end

      val skip = named_variable (prefix ^ "skip") numSyntax.num
      val loop_var = named_variable (prefix ^ "loop")
        (function_type
          ([numSyntax.num, numSyntax.num], result_ty))
      val body = build plan [] skip
      val loop_definition = TotalDefn.Define
        [HOLPP.ANTIQUOTE
          (boolSyntax.mk_eq
            (Term.list_mk_comb (loop_var, [size, skip]), body))]
      val _ =
        if Refute_Core.Private.enabled 3 then
          Refute_Core.Private.say 3
            ("Refute synthesized HOL loop:\n" ^
             Parse.thm_to_string loop_definition ^ "\n")
        else ()
      val _ = translate_checked prefix payloads loop_definition
      val loop = definition_head loop_definition
      fun application size_value skip_value =
        Term.list_mk_comb
          (loop, [numeral size_value, numeral skip_value])
    in
      {variables = variables, result_ty = result_ty,
       application = application}
    end

  fun define_exhaustive_enum prefix payloads plan generators programs
      enum_fuel =
    let
      val variables = plan_variables plan
      val value_ty = env_type variables
      val list_result_ty = listSyntax.mk_list_type value_ty
      val result_ty = result_type variables
      val size = named_variable (prefix ^ "size") numSyntax.num
      val enum_definition = define_enumerators prefix payloads programs
      val enumerators = #enumerators enum_definition
      val enum_generator_types = #generator_types enum_definition
      val enum_generators = map (fn ty =>
        Term.mk_comb (#exhaustive (generator_for ty generators), size))
        enum_generator_types
      val empty = listSyntax.mk_list ([], value_ty)
      fun singleton value = listSyntax.mk_list ([value], value_ty)
      fun bind values variable body = listSyntax.mk_flat
        (listSyntax.mk_map (Term.mk_abs (variable, body), values))

      fun enum_values relation mode inputs =
        Refute_EvalEnum.application
          (hol_enumerator_for enumerators relation mode)
          enum_generators inputs enum_fuel

      fun smart_guard_values predicate version env =
        let
          val programs = map #program enumerators
          val (program, ins) =
            case Refute_EvalEnum.smart_guard_lookup
                {relation = predicate, version = version} programs of
              SOME found => found
            | NONE => raise Unsupported "stale smart Guard"
        in
          enum_values (#relation program) (#mode program)
            (map (substitute env) ins)
        end

      fun build current env =
        case current of
            Refute_Eval.Prune => empty
          | Refute_Eval.Test tm =>
              boolSyntax.mk_cond
                (substitute env tm, empty,
                 singleton (env_term variables env))
          | Refute_Eval.Guard (tm, next) =>
              boolSyntax.mk_cond
                (substitute env tm, build next env, empty)
          | Refute_Eval.SmartGuard {predicate, version, cont} =>
              boolSyntax.mk_cond
                (listSyntax.mk_null
                   (smart_guard_values predicate version env),
                 empty, build cont env)
          | Refute_Eval.Enum {rel, mode, ins, outs, cont, ...} =>
              let
                val data = hol_enumerator_for enumerators rel mode
                val output = named_variable (fresh_prefix () ^ "enum_out")
                  (tuple_type (#output_types data))
                val values = enum_values rel mode
                  (map (substitute env) ins)
                val body = make_pattern_matches outs
                  (unpack_terms (#output_types data) output) env empty
                  (fn extended => build cont extended)
              in
                bind values output body
              end
          | Refute_Eval.Bind (variable, tm, _, next) =>
              let
                val value = named_variable
                  (fresh_prefix () ^ "bound") (Term.type_of variable)
              in
                boolSyntax.mk_let
                  (Term.mk_abs
                    (value, build next ((variable, value) :: env)),
                   substitute env tm)
              end
          | Refute_Eval.Split (scrutinee, branches) =>
              make_split scrutinee branches env empty
                (fn next => fn branch_env => build next branch_env)
          | Refute_Eval.Gen (variable, next) =>
              let
                val values = Term.mk_comb
                  (#exhaustive (generator_for (Term.type_of variable)
                    generators), size)
              in
                bind values variable
                  (build next ((variable, variable) :: env))
              end

      val loop_var = named_variable (prefix ^ "loop")
        (function_type ([numSyntax.num], list_result_ty))
      val loop_definition = TotalDefn.Define
        [HOLPP.ANTIQUOTE (boolSyntax.mk_eq
          (Term.mk_comb (loop_var, size), build plan []))]
      val _ = if Refute_Core.Private.enabled 3 then
          Refute_Core.Private.say 3
            ("Refute synthesized HOL loop:\n" ^
             Parse.thm_to_string loop_definition ^ "\n")
        else ()
      val _ = translate_checked prefix payloads loop_definition
      val loop = definition_head loop_definition
      fun application size_value skip_value =
        HolKernel.list_mk_icomb ``refute_cv$refute_cv_first_hit``
          [Term.mk_comb (loop, numeral size_value),
           numeral skip_value]
    in
      {variables = variables, result_ty = result_ty,
       application = application}
    end

  fun define_random prefix payloads plan generators =
    let
      val variables = plan_variables plan
      val value_ty = env_type variables
      val option_ty = optionSyntax.mk_option value_ty
      val final_ty = sumSyntax.mk_sum
        (numSyntax.num, pairSyntax.mk_prod (numSyntax.num, value_ty))
      val size = named_variable (prefix ^ "size") numSyntax.num
      val loop_var = named_variable (prefix ^ "loop")
        (function_type
          ([numSyntax.num, numSyntax.num, numSyntax.num], final_ty))

      fun build current env state =
        case current of
            Refute_Eval.Prune => no_hit variables state
          | Refute_Eval.Test tm =>
              boolSyntax.mk_cond
                (substitute env tm, no_hit variables state,
                 hit variables state env)
          | Refute_Eval.Guard (tm, next) =>
              boolSyntax.mk_cond
                (substitute env tm, build next env state,
                 no_hit variables state)
          | Refute_Eval.SmartGuard {predicate, cont, ...} =>
              boolSyntax.mk_cond
                (substitute env predicate, build cont env state,
                 no_hit variables state)
          | Refute_Eval.Enum _ =>
              raise Unsupported
                "smart generators currently require exhaustive testing"
          | Refute_Eval.Bind (variable, tm, _, next) =>
              let
                val value = named_variable
                  (fresh_prefix () ^ "bound") (Term.type_of variable)
              in
                boolSyntax.mk_let
                  (Term.mk_abs
                    (value, build next ((variable, value) :: env) state),
                   substitute env tm)
              end
          | Refute_Eval.Split (scrutinee, branches) =>
              make_split scrutinee branches env (no_hit variables state)
                (fn next => fn branch_env =>
                  build next branch_env state)
          | Refute_Eval.Gen (variable, next) =>
              let
                val stem = fresh_prefix ()
                val ty = Term.type_of variable
                val value = named_variable (stem ^ "draw") ty
                val next_state = named_variable
                  (stem ^ "next_state") numSyntax.num
                val draw = Term.list_mk_comb
                  (#random (generator_for ty generators), [size, state])
              in
                pairSyntax.mk_plet
                  (pairSyntax.mk_pair (value, next_state), draw,
                   build next ((variable, value) :: env) next_state)
              end

      val state = named_variable (prefix ^ "state") numSyntax.num
      val n = named_variable (prefix ^ "n") numSyntax.num
      val next_state = named_variable
        (prefix ^ "next_state") numSyntax.num
      val answer = named_variable (prefix ^ "answer") option_ty
      val found = named_variable (prefix ^ "found") value_ty
      val zero_lhs = Term.list_mk_comb
        (loop_var, [numeral 0, size, state])
      val zero_rhs = sumSyntax.mk_inl (state,
        pairSyntax.mk_prod (numSyntax.num, value_ty))
      val suc_lhs = Term.list_mk_comb
        (loop_var, [numSyntax.mk_suc n, size, state])
      val recurse = Term.list_mk_comb
        (loop_var, [n, size, next_state])
      val found_result = sumSyntax.mk_inr
        (pairSyntax.mk_pair (next_state, found), numSyntax.num)
      val choose = make_option_case answer recurse found found_result
      val suc_rhs = pairSyntax.mk_plet
        (pairSyntax.mk_pair (next_state, answer), build plan [] state,
         choose)
      val loop_definition = TotalDefn.Define
        [HOLPP.ANTIQUOTE
          (boolSyntax.mk_conj
            (boolSyntax.mk_eq (zero_lhs, zero_rhs),
             boolSyntax.mk_eq (suc_lhs, suc_rhs)))]
      val _ =
        if Refute_Core.Private.enabled 3 then
          Refute_Core.Private.say 3
            ("Refute synthesized HOL loop:\n" ^
             Parse.thm_to_string loop_definition ^ "\n")
        else ()
      val _ = translate_checked prefix payloads loop_definition
      val loop = definition_head loop_definition
      fun application draws size_value state_value =
        Term.list_mk_comb
          (loop,
           [numeral draws, numeral size_value,
            numSyntax.mk_numeral (Arbnum.fromLargeInt state_value)])
    in
      {variables = variables, result_ty = final_ty,
       application = application}
    end

  fun cv_term_for application =
    let
      val representation = cv_repLib.cv_rep_for [] application
      val precondition = cv_miscLib.cv_rep_pre (Thm.concl representation)
      val _ =
        if Term.aconv precondition boolSyntax.T then ()
        else raise Precondition "translated loop"
    in
      cv_miscLib.cv_rep_cv_tm (Thm.concl representation)
    end

  type card_runner = Refute_Eval.run_input -> Refute_Eval.run_result

  fun evaluator_for application result_ty =
    let
      val sample = application ()
      val cv_sample = cv_term_for sample
      val evaluator = cv_computeLib.cv_compute
        (cv_transLib.cv_eqs_for cv_sample)
      val decoder = cv_typeLib.to_term_for result_ty
      fun theorem_rhs theorem = boolSyntax.rhs (Thm.concl theorem)
      fun evaluate tm =
        let
          val cv_application = cv_term_for tm
          val literal = theorem_rhs (evaluator cv_application)
          val decoded = theorem_rhs
            (computeLib.EVAL_CONV (Term.mk_comb (decoder, literal)))
        in
          decoded
        end
    in
      evaluate
    end

  fun compile_card strategy plan generators programs enum_fuel state_ref =
    let
      val prefix = fresh_prefix ()
      val payloads = plan_payloads plan
    in
      Refute_Eval.ground_strategy strategy
        {exhaustive = fn () =>
            let
              val uses_enum = Refute_Eval.plan_uses_enum plan
              val program =
                if uses_enum then
                  define_exhaustive_enum prefix payloads plan generators
                    programs enum_fuel
                else
                  define_exhaustive_search prefix payloads plan generators
              val evaluate = evaluator_for
                (fn () => #application program 0 0) (#result_ty program)
              val complete =
                not uses_enum andalso
                List.all (Option.isSome o Refute_Gen.enumerate)
                  (plan_generator_types plan)
              fun run {size, ignored, ...} =
                let
                  val bounded_size = Int.max (0, size)
                  fun search skip =
                    let
                      val decoded = evaluate
                        (#application program bounded_size skip)
                      val (_, answer) = pairSyntax.dest_pair decoded
                    in
                      if optionSyntax.is_none answer then
                        Refute_Eval.Exhausted {complete = complete}
                      else
                        let
                          val found =
                            {env = decode_env (#variables program)
                               (optionSyntax.dest_some answer),
                             ground_env = NONE, case_tree = NONE,
                             genuine = true, run_depth = NONE}
                        in
                          if Refute_Eval.ignored_candidate found ignored then
                            search (skip + 1)
                          else Refute_Eval.CexFound found
                        end
                    end
                in
                  (* The skip argument denotes candidates in this particular
                     stream, not entries in the caller's structural ignore
                     list. *)
                  search 0
                end
            in
              run
            end,
         random = fn _ =>
            let
              val program = define_random prefix payloads plan generators
              val evaluate = evaluator_for
                (fn () => #application program 0 0 (!state_ref))
                (#result_ty program)
              val complete = null (plan_generator_types plan)
              fun run {size, draws, ignored, ...} =
                let
                  val decoded = evaluate
                    (#application program (Int.max (0, draws))
                      (Int.max (0, size)) (!state_ref))
                in
                  if sumSyntax.is_inl decoded then
                    let
                      val (state_tm, _) = sumSyntax.dest_inl decoded
                      val _ = state_ref := Arbnum.toLargeInt
                        (numSyntax.dest_numeral state_tm)
                    in
                      Refute_Eval.Exhausted {complete = complete}
                    end
                  else
                    let
                      val (result, _) = sumSyntax.dest_inr decoded
                      val (state_tm, value) = pairSyntax.dest_pair result
                      val _ = state_ref := Arbnum.toLargeInt
                        (numSyntax.dest_numeral state_tm)
                    in
                      let
                        val found =
                          {env = decode_env (#variables program) value,
                           ground_env = NONE, case_tree = NONE,
                           genuine = true, run_depth = NONE}
                      in
                        if Refute_Eval.ignored_candidate found ignored then
                          Refute_Eval.Exhausted {complete = false}
                        else Refute_Eval.CexFound found
                      end
                    end
                end
            in
              run
            end}
    end

  fun compile_plans (config : Refute_Core.config) strategy plans =
    let
      val programs = Refute_EvalEnum.prepare strategy plans
      val all_types = distinct_types
        (List.concat (List.map plan_generator_types plans) @
         List.concat (map Refute_SmartGen.enumerator_gen_types programs))
      val _ = List.app validate_supported all_types
      val _ =
        case partial_constant plans of
            NONE => ()
          | SOME name => raise Precondition name
      val last_stats = ref []
      val state_ref = ref
        (Refute_Eval.ground_strategy strategy
          {exhaustive = fn () => 0, random = fn seed => seed})
      val runners = ref ([] : (int * card_runner) list)
      val active : unit Refute_EvalEnum.held_bracket =
        Refute_EvalEnum.held_bracket (fn () => runners := [])

      fun close () = Refute_EvalEnum.close_held_bracket active

      fun start () =
        Refute_EvalEnum.start_held_bracket active (fn () => ())

      fun runner card =
        case List.find (fn (old_card, _) => old_card = card) (!runners) of
            SOME (_, run) => run
          | NONE =>
              let
                val plan = List.nth (plans, card - 1)
                val types = distinct_types
                  (plan_generator_types plan @
                   Refute_EvalEnum.generator_types programs)
                val generators = synthesise_generators types
                val run = compile_card strategy plan generators programs
                  (Int.max (0, #depth (#qc config))) state_ref
                val _ = runners := (card, run) :: !runners
              in
                run
              end

      (* Generator synthesis, definitions, and cv translation are
         applicability checks, not evaluation results.  Force them while
         Auto can still select the next substrate. *)
      val _ =
        (start ();
         List.app (fn card => ignore (runner card))
           (Portable.upto 1 (length plans)))
        handle e => (close (); raise e)

      fun run input =
        let
          val _ = start ()
          val result = runner (#card input) input
          val tests =
            Refute_Eval.ground_strategy strategy
              {exhaustive = fn () => 0,
               random = fn _ => Int.max (0, #draws input)}
          val _ = last_stats := [("tests", tests), ("match_failures", 0)]
        in
          result
        end
        handle Precondition name =>
                 Refute_Eval.GaveUp ("cv: precondition for " ^ name)
             | Unsupported reason =>
                 Refute_Eval.GaveUp ("cv: " ^ reason)
             | Feedback.HOL_ERR error =>
                 Refute_Eval.GaveUp (hol_error_reason error)
             | Timeout.TIMEOUT _ =>
                 Refute_Eval.GaveUp "cv: chunk timed out"
    in
      (* Bounding each run keeps a single cv_eval call (and hence the
         span between timeout checks) small; the driver reads max_chunk
         instead of knowing which substrate it is talking to. *)
      Refute_Eval.Compiled
        {run = run, close = close, max_chunk = SOME 1024,
         last_stats = last_stats}
    end
    handle Precondition name =>
             Refute_Eval.Inapplicable ["cv: precondition for " ^ name]
         | Refute_EvalEnum.Invalid reason =>
             Refute_Eval.Inapplicable [reason]
         | Unsupported reason =>
             Refute_Eval.Inapplicable ["cv: " ^ reason]
         | Feedback.HOL_ERR error =>
             Refute_Eval.Inapplicable [hol_error_reason error]

  fun compile config strategy problem =
    Refute_Eval.with_plans problem (fn plans =>
      compile_plans config strategy plans)

  (* Selftest-only stream hook.  Supported plans run through the production
     cv loop.  Values outside its first-order result fragment still take
     every random draw through cv_eval, with an independent reconstruction
     of the normative consumption discipline. *)
  fun dump_plan current =
    case current of
        Refute_Eval.Test _ => Refute_Eval.Test boolSyntax.F
      | Refute_Eval.Gen (variable, next) =>
          Refute_Eval.Gen (variable, dump_plan next)
      | _ => raise Unsupported "candidate dump requires a Gen chain"

  fun dump_cv_loop {plan, seed, size, count} =
    case compile Refute_Core.default_config
        (Refute_Eval.Random {seed = seed})
        (Refute_Eval.Plans [dump_plan plan]) of
        Refute_Eval.Inapplicable reasons => CvInapplicable reasons
      | Refute_Eval.Compiled test =>
          CvSuccess (Refute_Eval.dump_stream test
            {size = size, count = count})

  fun cv_dump_rand_below bound state =
    let
      fun num value = numSyntax.mk_numeral (Arbnum.fromLargeInt value)
      val application = Term.list_mk_comb
        (rand_below_tm, [num bound, num state])
      val theorem = cv_transLib.cv_eval application
      val result = boolSyntax.rhs (Thm.concl theorem)
      val (value_tm, state_tm) = pairSyntax.dest_pair result
      fun dest tm = Arbnum.toLargeInt (numSyntax.dest_numeral tm)
    in
      (dest value_tm, dest state_tm)
    end

  (* The compute substrate's random family, replayed with every draw
     routed through cv_eval.  Sharing one implementation keeps the
     consumption discipline identical across substrates by construction. *)
  fun cv_dump_random_term ty size state =
    let
      fun draw bound current =
        if bound <= 0 orelse bound > Refute_Eval.rand_below_limit then
          raise Unsupported "candidate dump random bound exceeds 2^32"
        else cv_dump_rand_below bound current
      fun custom _ _ _ =
        raise Unsupported
          "custom generator is unavailable in cv candidate dump"
    in
      Refute_EvalCompute.random_entry_with draw custom
        (Refute_Gen.spec_of ty) (Int.max (0, size)) state
    end

  fun dump_cv_fallback {plan, seed, size, count} =
    let
      fun variables current =
        case current of
            Refute_Eval.Gen (variable, next) =>
              variable :: variables next
          | Refute_Eval.Test _ => []
          | _ => raise Unsupported "candidate dump requires a Gen chain"
      val generated = variables plan
      fun candidate [] state values = (rev values, state)
        | candidate (variable :: rest) state values =
            let
              val (value, next) = cv_dump_random_term
                (Term.type_of variable) size state
            in
              candidate rest next (value :: values)
            end
      fun loop 0 _ candidates = rev candidates
        | loop remaining state candidates =
            let val (values, next) = candidate generated state []
            in loop (remaining - 1) next (values :: candidates) end
    in
      loop (Int.max (0, count)) seed []
    end

  fun dump_cv_random_candidates (arguments as {plan, ...}) =
    let
      val supported =
        (List.app validate_supported (plan_generator_types plan); true)
        handle Unsupported _ => false
    in
      if not supported then dump_cv_fallback arguments
      else
        case dump_cv_loop arguments of
            CvSuccess candidates => candidates
          | CvInapplicable reasons =>
              raise Fail (String.concatWith "; " reasons)
    end

  val cv_substrate : Refute_Eval.substrate =
    {name = "cv", priority = 20,
     accepts =
       (fn Refute_Eval.Plans _ => true | Refute_Eval.Pnf _ => false),
     preflight = NONE, compile = compile}

  fun register_substrate () =
    Refute_Eval.register_substrate cv_substrate

  val _ = register_substrate ()
end
