structure Refute_ModelFinder_Preproc = struct
  type term = Term.term
  type hol_type = Type.hol_type
  type context = Refute_ModelFinder_HOL.mf_context

  structure MFH = Refute_ModelFinder_HOL
  structure MFN = Refute_ModelFinder_Names
  structure MFU = Refute_ModelFinder_Util

  val value_var_prefix = MFN.reserved_prefix ^ "v"
  val max_skolem_depth = 3
  val axioms_max_depth = 255
  val quantifier_cluster_threshold = 7

  fun err function message =
    Feedback.mk_HOL_ERR "Refute_ModelFinder_Preproc" function message

  fun variable_name variable = #1 (Term.dest_var variable)

  fun aconv_member term = List.exists (Term.aconv term)

  fun add_aconv term terms =
    if aconv_member term terms then terms else terms @ [term]

  fun is_value_var term =
    case Lib.total Term.dest_var term of
        SOME (name, _) => String.isPrefix value_var_prefix name
      | NONE => false

  fun is_generated_const term =
    case Lib.total Term.dest_var term of
        SOME (name, _) =>
          MFN.is_reserved_name name andalso not (is_value_var term)
      | NONE => false

  fun is_user_free term =
    Term.is_var term andalso
    not (MFN.is_reserved_name (variable_name term))

  fun is_bound_or_value_var bound term =
    is_value_var term orelse aconv_member term bound

  fun term_occurs needle haystack =
    Term.aconv needle haystack orelse
    if Term.is_comb haystack then
      let val (function, argument) = Term.dest_comb haystack
      in term_occurs needle function orelse term_occurs needle argument end
    else if Term.is_abs haystack then
      term_occurs needle (#2 (Term.dest_abs haystack))
    else
      false

  fun substitute variable replacement term =
    Term.subst [{redex = variable, residue = replacement}] term

  fun close_form term =
    let
      (* Isabelle's close_form closes schematic Vars, never user Frees.
         M3's only schematic HOL4 analogue is a pulled-out value variable. *)
      fun closable variable = is_value_var variable
      fun add_frees candidate seen =
        List.foldl (fn (variable, result) =>
          if closable variable then add_aconv variable result else result)
          seen (Term.free_vars_lr candidate)
      fun close_new old current body =
        boolSyntax.list_mk_forall
          (List.drop (current, length old), body)
      fun recurse seen candidate =
        if boolSyntax.is_imp candidate then
          let
            val (premise, conclusion) = boolSyntax.dest_imp candidate
            val extended = add_frees premise seen
            val body = boolSyntax.mk_imp
              (premise, recurse extended conclusion)
          in
            close_new seen extended body
          end
        else
          let val extended = add_frees candidate seen
          in close_new seen extended candidate end
    in
      recurse [] term
    end

  fun is_higher_order_type ty =
    case Lib.total Type.dom_rng ty of
        SOME _ => true
      | NONE =>
          (case Lib.total Type.dest_thy_type ty of
               SOME {Args, ...} => List.exists is_higher_order_type Args
             | NONE => false)

  fun skolemize_term_and_more
        (context as {skolems, ...} : context) skolem_depth term =
    let
      fun positive_existential polarity existential =
        case (polarity, existential) of
            (MFU.Pos, true) => true
          | (MFU.Neg, false) => true
          | _ => false
      fun skolem_type dependencies result =
        boolSyntax.list_mk_fun (map Term.type_of dependencies, result)
      fun recurse dependencies skolemizable polarity candidate =
        if boolSyntax.is_forall candidate orelse
           boolSyntax.is_exists candidate then
          let
            val existential = boolSyntax.is_exists candidate
            val (variable, body) =
              if existential then boolSyntax.dest_exists candidate
              else boolSyntax.dest_forall candidate
            val occurs = Term.free_in variable body
            fun keep () =
              let
                val transformed = recurse (dependencies @ [variable])
                  (skolemizable andalso
                   not (is_higher_order_type (Term.type_of variable)))
                  polarity body
              in
                if existential then
                  boolSyntax.mk_exists (variable, transformed)
                else
                  boolSyntax.mk_forall (variable, transformed)
              end
          in
            if not occurs then
              recurse dependencies skolemizable polarity body
            else if positive_existential polarity existential andalso
                    skolemizable andalso
                    length dependencies <= skolem_depth then
              let
                val serial = length (!skolems) + 1
                val original = variable_name variable
                val arity = length dependencies
                val skolem = MFN.mk_skolem arity serial original
                  (skolem_type dependencies (Term.type_of variable))
                val application =
                  Term.list_mk_comb (skolem, dependencies)
                val generated_name = variable_name skolem
                val enclosing_names =
                  rev (map variable_name dependencies)
                val _ = skolems :=
                  (generated_name, enclosing_names) :: !skolems
                val transformed = recurse dependencies skolemizable
                  polarity body
              in
                if null dependencies then
                  substitute variable application transformed
                else
                  boolSyntax.mk_let
                    (Term.mk_abs (variable, transformed), application)
              end
            else
              keep ()
          end
        else if boolSyntax.is_neg candidate then
          boolSyntax.mk_neg (recurse dependencies skolemizable
            (MFU.flip_polarity polarity)
            (boolSyntax.dest_neg candidate))
        else if boolSyntax.is_imp candidate then
          let val (left, right) = boolSyntax.dest_imp candidate
          in
            boolSyntax.mk_imp
              (recurse dependencies skolemizable
                 (MFU.flip_polarity polarity) left,
               recurse dependencies skolemizable polarity right)
          end
        else if boolSyntax.is_conj candidate then
          let
            val (left, right) = boolSyntax.dest_conj candidate
            val left' = recurse dependencies skolemizable polarity left
            val right' = recurse dependencies skolemizable polarity right
          in
            if Term.aconv left' boolSyntax.T then right'
            else if Term.aconv right' boolSyntax.T then left'
            else if Term.aconv left' boolSyntax.F orelse
                    Term.aconv right' boolSyntax.F then boolSyntax.F
            else boolSyntax.mk_conj (left', right')
          end
        else if boolSyntax.is_disj candidate then
          let
            val (left, right) = boolSyntax.dest_disj candidate
            val left' = recurse dependencies skolemizable polarity left
            val right' = recurse dependencies skolemizable polarity right
          in
            if Term.aconv left' boolSyntax.F then right'
            else if Term.aconv right' boolSyntax.F then left'
            else if Term.aconv left' boolSyntax.T orelse
                    Term.aconv right' boolSyntax.T then boolSyntax.T
            else boolSyntax.mk_disj (left', right')
          end
        else if boolSyntax.is_let candidate then
          let val (function, argument) = boolSyntax.dest_let candidate
          in
            boolSyntax.mk_let
              (recurse dependencies skolemizable polarity function,
               argument)
          end
        else if Term.is_comb candidate then
          let val (function, argument) = Term.dest_comb candidate
          in
            MFH.s_betapply
              (recurse dependencies false polarity function,
               recurse dependencies false MFU.Neut argument)
          end
        else if Term.is_abs candidate then
          let val (variable, body) = Term.dest_abs candidate
          in
            Term.mk_abs (variable,
              recurse dependencies skolemizable polarity body)
          end
        else
          candidate
    in
      recurse [] true MFU.Pos term
    end

  fun destroy_set_Collect term =
    if boolSyntax.is_IN term then
      let
        val (element, set) = boolSyntax.dest_IN term
        val transformed_element = destroy_set_Collect element
        val transformed_set = destroy_set_Collect set
      in
        if Term.is_abs transformed_set then
          destroy_set_Collect
            (MFH.s_betapply (transformed_set, transformed_element))
        else
          boolSyntax.mk_IN (transformed_element, transformed_set)
      end
    else if Term.is_comb term then
      let val (function, argument) = Term.dest_comb term
      in
        MFH.s_betapply
          (destroy_set_Collect function, destroy_set_Collect argument)
      end
    else if Term.is_abs term then
      let val (variable, body) = Term.dest_abs term
      in Term.mk_abs (variable, destroy_set_Collect body) end
    else
      term

  fun is_pair_type ty = MFH.is_pair_type ty

  fun is_set_type ty =
    case Lib.total Type.dom_rng ty of
        SOME (_, range) => range = Type.bool
      | NONE => false

  fun heavy_variables term =
    List.filter (not o is_generated_const) (Term.free_vars_lr term)

  fun has_heavy_vars term =
    case heavy_variables term of
        [] => false
      | [variable] =>
          let val ty = Term.type_of variable
          in is_higher_order_type ty orelse is_set_type ty orelse
             is_pair_type ty
          end
      | _ => true

  fun fully_applied_constructor term =
    let
      val (head, arguments) = HolKernel.strip_comb term
    in
      if Term.is_const head andalso MFH.is_constr head andalso
         length arguments = length (MFH.constructor_arg_types head) then
        SOME (head, arguments)
      else
        NONE
    end

  fun is_function_set_or_pair ty =
    is_higher_order_type ty orelse is_set_type ty orelse is_pair_type ty

  fun fresh_value_var avoids serial ty =
    Term.variant avoids
      (MFN.mk_reserved_var
        (value_var_prefix ^ Int.toString serial) ty)

  fun pulled_lookup term pulled =
    Option.map #2 (List.find (fn (other, _) => Term.aconv other term)
      pulled)

  fun pull_candidate avoids forbidden relax candidate pulled =
    case fully_applied_constructor candidate of
        NONE => (candidate, pulled)
      | SOME _ =>
          if relax orelse is_function_set_or_pair (Term.type_of candidate)
             orelse not (has_heavy_vars candidate) orelse
             List.exists (fn variable => Term.free_in variable candidate)
               forbidden then
            (candidate, pulled)
          else
            (case pulled_lookup candidate pulled of
                 SOME variable => (variable, pulled)
               | NONE =>
                   let
                     val variable = fresh_value_var
                       (avoids @ map #2 pulled) (length pulled)
                       (Term.type_of candidate)
                   in
                     (variable, pulled @ [(candidate, variable)])
                   end)

  fun equations_for_pulled pulled =
    map (fn (term, variable) => boolSyntax.mk_eq (variable, term))
      pulled

  fun pull_out_universal_constrs context def term =
    let
      val avoids = Term.all_vars term
      fun recurse forbidden relaxed candidate pulled =
        if boolSyntax.is_eq candidate then
          let
            val (left, right) = boolSyntax.dest_eq candidate
            val (right', pulled') =
              if def then (right, pulled)
              else recurse forbidden false right pulled
            val (left', pulled'') =
              recurse forbidden false left pulled'
          in
            (boolSyntax.mk_eq (left', right'), pulled'')
          end
        else if boolSyntax.is_imp candidate then
          if def then (candidate, pulled)
          else
            let
              val (left, right) = boolSyntax.dest_imp candidate
              val (right', pulled') =
                recurse forbidden false right pulled
              val (left', pulled'') =
                recurse forbidden false left pulled'
            in
              (boolSyntax.mk_imp (left', right'), pulled'')
            end
        else if boolSyntax.is_forall candidate orelse
                boolSyntax.is_exists candidate then
          let
            val is_exists = boolSyntax.is_exists candidate
            val (variable, body) =
              if is_exists then boolSyntax.dest_exists candidate
              else boolSyntax.dest_forall candidate
            val (body', pulled') =
              recurse (variable :: forbidden) relaxed body pulled
            val result =
              if is_exists then boolSyntax.mk_exists (variable, body')
              else boolSyntax.mk_forall (variable, body')
          in
            (result, pulled')
          end
        else if Term.is_abs candidate then
          let
            val (variable, body) = Term.dest_abs candidate
            val (body', pulled') =
              recurse (variable :: forbidden) relaxed body pulled
          in
            (Term.mk_abs (variable, body'), pulled')
          end
        else if Term.is_comb candidate then
          let
            val (head, arguments) = HolKernel.strip_comb candidate
            fun do_arguments [] result current =
                  (rev result, current)
              | do_arguments (argument :: rest) result current =
                  let
                    val (argument', current') =
                      recurse forbidden false argument current
                  in
                    do_arguments rest (argument' :: result) current'
                  end
            val (arguments', pulled') =
              do_arguments arguments [] pulled
            val rebuilt = Term.list_mk_comb (head, arguments')
          in
            pull_candidate avoids forbidden relaxed rebuilt pulled'
          end
        else
          pull_candidate avoids forbidden relaxed candidate pulled
      val (conclusion, pulled) = recurse [] def term []
    in
      boolSyntax.list_mk_imp
        (equations_for_pulled pulled, conclusion)
    end

  fun smart_conj terms =
    let
      val useful = List.filter (not o Term.aconv boolSyntax.T) terms
    in
      if List.exists (Term.aconv boolSyntax.F) useful then boolSyntax.F
      else if null useful then boolSyntax.T
      else boolSyntax.list_mk_conj useful
    end

  fun pull_out_existential_constrs context term =
    let
      val avoids = Term.all_vars term
      fun recurse outer candidate =
        if boolSyntax.is_exists candidate then
          let
            val (variable, body) = boolSyntax.dest_exists candidate
            val (body', pulled) = collect outer [variable] body []
            val equations = equations_for_pulled pulled
            val fresh = map #2 pulled
            val matrix = smart_conj (equations @ [body'])
          in
            boolSyntax.mk_exists (variable,
              boolSyntax.list_mk_exists (fresh, matrix))
          end
        else if boolSyntax.is_forall candidate then
          let val (variable, body) = boolSyntax.dest_forall candidate
          in boolSyntax.mk_forall (variable,
               recurse (variable :: outer) body)
          end
        else if Term.is_abs candidate then
          let val (variable, body) = Term.dest_abs candidate
          in Term.mk_abs (variable, recurse (variable :: outer) body) end
        else if Term.is_comb candidate then
          let val (function, argument) = Term.dest_comb candidate
          in MFH.s_betapply (recurse outer function,
               recurse outer argument) end
        else
          candidate
      and collect outer existentials candidate pulled =
        if boolSyntax.is_exists candidate then
          (recurse outer candidate, pulled)
        else if Term.is_abs candidate then
          let val (variable, body) = Term.dest_abs candidate
          in
            (Term.mk_abs (variable, recurse (variable :: outer) body),
             pulled)
          end
        else if Term.is_comb candidate then
          let
            val (head, arguments) = HolKernel.strip_comb candidate
            fun do_arguments [] result current =
                  (rev result, current)
              | do_arguments (argument :: rest) result current =
                  let
                    val (argument', current') =
                      collect outer existentials argument current
                  in
                    do_arguments rest (argument' :: result) current'
                  end
            val (arguments', pulled') =
              do_arguments arguments [] pulled
            val rebuilt = Term.list_mk_comb (head, arguments')
          in
            pull_candidate avoids outer false rebuilt pulled'
          end
        else
          pull_candidate avoids outer false candidate pulled
    in
      recurse [] term
    end

  fun is_constructor_pattern bound term =
    if is_bound_or_value_var bound term then
      true
    else
      let
        val (head, arguments) = HolKernel.strip_comb term
      in
        Term.is_const head andalso MFH.is_nonfree_constr head andalso
        length arguments = length (MFH.constructor_arg_types head) andalso
        List.all (is_constructor_pattern bound) arguments
      end
      handle HOL_ERR _ => false

  fun count_occurrences needle term =
    let
      val here = if Term.aconv needle term then 1 else 0
    in
      if Term.is_comb term then
        let val (function, argument) = Term.dest_comb term
        in here + count_occurrences needle function +
           count_occurrences needle argument
        end
      else if Term.is_abs term then
        here + count_occurrences needle (#2 (Term.dest_abs term))
      else
        here
    end

  fun destructible_constructor term =
    let
      val (head, arguments) = HolKernel.strip_comb term
      val constructor = Term.is_const head andalso
        (MFH.is_constr head orelse MFH.is_pair_constructor head orelse
         MFH.is_suc_constructor head)
    in
      if constructor andalso
         length arguments = length (MFH.constructor_arg_types head) then
        SOME (head, arguments)
      else
        NONE
    end handle HOL_ERR _ => NONE

  fun destroy_pulled_out_constrs context axiom strong term =
    let
      val let_inline_threshold = 20
      fun eligible_for_duplication bound candidate =
        let
          val variables = List.filter (fn variable =>
            is_value_var variable orelse aconv_member variable bound)
            (Term.free_vars_lr candidate)
        in
          case variables of
              [] => true
            | _ =>
                let
                  val variable_cost = List.foldl (fn (variable, cost) =>
                    Int.max (MFH.typical_card_of_type
                      (Term.type_of variable), cost)) 0 variables
                  val result_cost =
                    MFH.typical_card_of_type (Term.type_of candidate)
                in
                  variable_cost <= result_cost
                end
        end
      fun share_value bound occurrences candidate build =
        let
          val duplication = IntInf.fromInt (occurrences - 1) *
            IntInf.fromInt (Term.term_size candidate - 1)
        in
          if duplication <= IntInf.fromInt let_inline_threshold orelse
             eligible_for_duplication bound candidate then
            build candidate
          else
            let
              val variable = Term.variant (Term.all_vars term)
                (Term.mk_var ("l", Term.type_of candidate))
            in
              boolSyntax.mk_let
                (Term.mk_abs (variable, build variable), candidate)
            end
        end
      fun recurse bound careful candidate =
        if boolSyntax.is_imp candidate then
          let val (left, right) = boolSyntax.dest_imp candidate
          in
            boolSyntax.mk_imp
              (recurse bound false left,
               recurse bound careful right)
          end
        else if boolSyntax.is_eq candidate then
          let val (left, right) = boolSyntax.dest_eq candidate
          in destroy_equation bound careful true left right end
        else if Term.is_abs candidate then
          let val (variable, body) = Term.dest_abs candidate
          in
            Term.mk_abs
              (variable, recurse (variable :: bound) careful body)
          end
        else if Term.is_comb candidate then
          let val (function, argument) = Term.dest_comb candidate
          in
            MFH.s_betapply
              (recurse bound careful function,
               recurse bound careful argument)
          end
        else
          candidate
      and destroy_equation bound careful first left right =
        if careful orelse
           not (strong orelse
             (is_constructor_pattern bound left andalso
              is_constructor_pattern bound right)) then
          if first then
            destroy_equation bound careful false right left
          else
            boolSyntax.mk_eq
              (recurse bound false right,
               recurse bound false left)
        else if axiom andalso is_value_var right andalso
                count_occurrences right term = 1 then
          boolSyntax.T
        else
          case destructible_constructor right of
              SOME (constructor, arguments) =>
                let
                  val argument_tys =
                    MFH.constructor_arg_types constructor
                  val indexed = ListPair.zip
                    (MFU.index_seq 0 (length arguments),
                     ListPair.zip (arguments, argument_tys))
                  fun constraints value =
                    let
                      val discriminator =
                        MFH.discriminate_value context constructor value
                      fun selector_equation (index, (argument, ty)) =
                        recurse bound false (boolSyntax.mk_eq
                          (argument,
                           MFH.select_nth_constr_arg context constructor
                             value index ty))
                    in
                      smart_conj
                        (discriminator :: map selector_equation indexed)
                    end
                in
                  share_value bound (length arguments + 1) left constraints
                end
            | NONE =>
                if first then
                  destroy_equation bound careful false right left
                else
                  boolSyntax.mk_eq
                    (recurse bound false right,
                     recurse bound false left)
    in
      recurse [] axiom term
    end

  fun curry_assms term =
    if boolSyntax.is_imp term then
      let
        val (premise, conclusion) = boolSyntax.dest_imp term
        val conclusion' = curry_assms conclusion
      in
        if boolSyntax.is_conj premise then
          boolSyntax.list_mk_imp
            (map curry_assms (boolSyntax.strip_conj premise), conclusion')
        else
          boolSyntax.mk_imp (curry_assms premise, conclusion')
      end
    else
      term

  fun destroy_universal_equalities term =
    let
      fun recurse premises candidate =
        if boolSyntax.is_imp candidate then
          let
            val (premise, conclusion) = boolSyntax.dest_imp candidate
            fun eliminate variable replacement =
              if is_value_var variable andalso
                 not (List.exists (Term.free_in variable) premises) andalso
                 not (Term.free_in variable replacement) then
                SOME (recurse premises
                  (substitute variable replacement conclusion))
              else
                NONE
            val assignment =
              if boolSyntax.is_eq premise then
                let val (left, right) = boolSyntax.dest_eq premise
                in
                  case eliminate left right of
                      result as SOME _ => result
                    | NONE => eliminate right left
                end
              else
                NONE
          in
            case assignment of
                SOME result => result
              | NONE => recurse (premises @ [premise]) conclusion
          end
        else
          boolSyntax.list_mk_imp (premises, candidate)
    in
      recurse [] term
    end

  fun destroy_existential_equalities term =
    let
      fun find_assignment variable seen [] = NONE
        | find_assignment variable seen (conjunct :: rest) =
            if boolSyntax.is_eq conjunct then
              let
                val (left, right) = boolSyntax.dest_eq conjunct
                fun assignment candidate replacement =
                  if Term.aconv candidate variable andalso
                     not (Term.free_in variable replacement) then
                    SOME (replacement, rev seen @ rest)
                  else
                    NONE
              in
                case assignment left right of
                    result as SOME _ => result
                  | NONE =>
                      (case assignment right left of
                           result as SOME _ => result
                         | NONE => find_assignment variable
                             (conjunct :: seen) rest)
              end
            else
              find_assignment variable (conjunct :: seen) rest
      fun process_cluster variables matrix =
        let
          fun kill [] conjuncts = smart_conj conjuncts
            | kill (variable :: rest) conjuncts =
                (case find_assignment variable [] conjuncts of
                     SOME (_, []) => boolSyntax.T
                   | SOME (replacement, remaining) =>
                       kill rest (map
                         (substitute variable replacement) remaining)
                   | NONE => boolSyntax.mk_exists
                       (variable, kill rest conjuncts))
        in
          kill variables (boolSyntax.strip_conj (recurse matrix))
        end
      and recurse candidate =
        if boolSyntax.is_exists candidate then
          let val (variables, matrix) = boolSyntax.strip_exists candidate
          in process_cluster variables matrix end
        else if Term.is_abs candidate then
          let val (variable, body) = Term.dest_abs candidate
          in Term.mk_abs (variable, recurse body) end
        else if Term.is_comb candidate then
          let val (function, argument) = Term.dest_comb candidate
          in MFH.s_betapply (recurse function, recurse argument) end
        else
          candidate
    in
      recurse term
    end

  fun simplify_constrs_and_sels context term =
    let
      fun selector_index head =
        case Lib.total Term.dest_var head of
            SOME (name, _) =>
              if MFN.is_sel name andalso MFN.sel_no_from_name name >= 0 then
                SOME (MFN.original_name name,
                      MFN.sel_no_from_name name)
              else
                NONE
          | NONE =>
              if Term.is_const head andalso
                 MFH.is_named_const {Thy = "pair", Name = "FST"} head then
                SOME ("pair$,", 0)
              else if Term.is_const head andalso
                      MFH.is_named_const
                        {Thy = "pair", Name = "SND"} head then
                SOME ("pair$,", 1)
              else
                NONE
      fun selector_projection head argument rest =
        case selector_index head of
            SOME (constructor_name, index) =>
              (let
                 val (constructor, arguments) =
                   HolKernel.strip_comb argument
                 val argument_tys =
                   MFH.constructor_arg_types constructor
               in
                 if Term.is_const constructor andalso
                    MFH.is_free_constr constructor andalso
                    constructor_name =
                      MFH.constructor_name constructor andalso
                    not (List.exists MFH.is_pair_type argument_tys) andalso
                    index < length arguments then
                   SOME (MFH.s_betapplys
                     (List.nth (arguments, index), rest))
                 else
                   NONE
               end
               handle HOL_ERR _ => NONE)
          | NONE => NONE
      fun recurse candidate =
        if Term.is_abs candidate then
          let val (variable, body) = Term.dest_abs candidate
          in Term.mk_abs (variable, recurse body) end
        else if Term.is_comb candidate then
          let
            val (head, arguments) = HolKernel.strip_comb candidate
            val head' = recurse head
            val arguments' = map recurse arguments
            val rebuilt = MFH.s_betapplys (head', arguments')
          in
            if Term.is_const head' andalso MFH.is_nonfree_constr head' andalso
               length arguments' =
                 length (MFH.constructor_arg_types head') then
              MFH.construct_value context head' arguments'
            else
              case arguments' of
                  first :: rest =>
                    Option.getOpt
                      (selector_projection head' first rest, rebuilt)
                | [] => rebuilt
          end
        else
          candidate
    in
      recurse term
    end

  fun distribute_quantifiers term =
    if boolSyntax.is_forall term then
      let
        val (variable, body) = boolSyntax.dest_forall term
      in
        if boolSyntax.is_conj body then
          let val (left, right) = boolSyntax.dest_conj body
          in
            boolSyntax.mk_conj
              (distribute_quantifiers
                 (boolSyntax.mk_forall (variable, left)),
               distribute_quantifiers
                 (boolSyntax.mk_forall (variable, right)))
          end
        else if boolSyntax.is_neg body then
          boolSyntax.mk_neg (distribute_quantifiers
            (boolSyntax.mk_exists
              (variable, boolSyntax.dest_neg body)))
        else if not (Term.free_in variable body) then
          distribute_quantifiers body
        else
          boolSyntax.mk_forall
            (variable, distribute_quantifiers body)
      end
    else if boolSyntax.is_exists term then
      let
        val (variable, raw_body) = boolSyntax.dest_exists term
        val body = distribute_quantifiers raw_body
      in
        if boolSyntax.is_disj body then
          let val (left, right) = boolSyntax.dest_disj body
          in
            boolSyntax.mk_disj
              (distribute_quantifiers
                 (boolSyntax.mk_exists (variable, left)),
               distribute_quantifiers
                 (boolSyntax.mk_exists (variable, right)))
          end
        else if boolSyntax.is_imp body then
          let val (left, right) = boolSyntax.dest_imp body
          in
            boolSyntax.mk_imp
              (distribute_quantifiers
                 (boolSyntax.mk_forall (variable, left)),
               distribute_quantifiers
                 (boolSyntax.mk_exists (variable, right)))
          end
        else if boolSyntax.is_neg body then
          boolSyntax.mk_neg (distribute_quantifiers
            (boolSyntax.mk_forall
              (variable, boolSyntax.dest_neg body)))
        else if not (Term.free_in variable body) then
          distribute_quantifiers body
        else
          boolSyntax.mk_exists (variable, body)
      end
    else if Term.is_abs term then
      let val (variable, body) = Term.dest_abs term
      in Term.mk_abs (variable, distribute_quantifiers body) end
    else if Term.is_comb term then
      let val (function, argument) = Term.dest_comb term
      in MFH.s_betapply
           (distribute_quantifiers function,
            distribute_quantifiers argument)
      end
    else
      term

  fun connective_parts conjunction term =
    if conjunction andalso boolSyntax.is_conj term then
      let val (left, right) = boolSyntax.dest_conj term
      in
        connective_parts conjunction right @
        connective_parts conjunction left
      end
    else if not conjunction andalso boolSyntax.is_disj term then
      let val (left, right) = boolSyntax.dest_disj term
      in
        connective_parts conjunction right @
        connective_parts conjunction left
      end
    else
      [term]

  fun same_connective term =
    if boolSyntax.is_conj term then SOME true
    else if boolSyntax.is_disj term then SOME false
    else NONE

  fun make_connection true terms = boolSyntax.list_mk_conj terms
    | make_connection false terms = boolSyntax.list_mk_disj terms

  fun push_quantifiers_inward term =
    let
      fun gather universal variables candidate =
        if (universal andalso boolSyntax.is_forall candidate) orelse
           (not universal andalso boolSyntax.is_exists candidate) then
          let
            val (variable, body) =
              if universal then boolSyntax.dest_forall candidate
              else boolSyntax.dest_exists candidate
          in
            gather universal (variables @ [variable]) body
          end
        else
          (variables, candidate)
      fun merge_groups variable groups =
        let
          val (yes, no) = List.partition
            (fn (_, used, _) => aconv_member variable used) groups
        in
          if null yes then no
          else
            let
              val used = List.foldl
                (fn ((_, vars, _), result) =>
                  List.foldl (fn (item, accumulated) =>
                    if aconv_member item accumulated then accumulated
                    else accumulated @ [item]) result vars)
                [] yes
              val size = List.foldl
                (fn ((_, _, cost), total) => total + cost) 0 yes *
                MFH.typical_card_of_type (Term.type_of variable)
            in
              (boolSyntax.T, used, size) :: no
            end
        end
      fun groups_cost groups =
        List.foldl (fn ((_, _, cost), total) => total + cost) 0 groups
      fun merge_in_order order groups =
        List.foldl (fn (variable, current) =>
          merge_groups variable current) groups order
      fun best_order variables groups =
        let
          fun cost order = groups_cost (merge_in_order order groups)
          fun choose (order, NONE) = SOME (cost order, order)
            | choose (order, SOME (best as (best_cost, _))) =
                let val candidate_cost = cost order
                in
                  if candidate_cost < best_cost then
                    SOME (candidate_cost, order)
                  else
                    SOME best
                end
        in
          #2 (valOf (List.foldl choose NONE
            (MFU.all_permutations variables)))
        end
      fun greedy_order [] _ = []
        | greedy_order variables groups =
            let
              fun remove chosen = List.filter
                (fn variable => not (Term.aconv chosen variable))
                  variables
              fun choose (variable, NONE) =
                    SOME (groups_cost (merge_groups variable groups),
                          variable)
                | choose (variable,
                    SOME (best as (best_cost, _))) =
                    let
                      val candidate_cost = groups_cost
                        (merge_groups variable groups)
                    in
                      if candidate_cost < best_cost then
                        SOME (candidate_cost, variable)
                      else
                        SOME best
                    end
              val chosen = #2 (valOf
                (List.foldl choose NONE variables))
            in
              chosen :: greedy_order (remove chosen)
                (merge_groups chosen groups)
            end
      fun build universal connective order groups =
        let
          fun step (variable, current) =
            let
              val (yes, no) = List.partition
                (fn (_, used) => aconv_member variable used) current
            in
              if null yes then no
              else
                let
                  val connected = make_connection connective
                    (map #1 yes)
                  val quantified =
                    if universal then
                      boolSyntax.mk_forall (variable, connected)
                    else
                      boolSyntax.mk_exists (variable, connected)
                  val used = List.foldl
                    (fn ((_, vars), result) =>
                      List.foldl (fn (item, accumulated) =>
                        if aconv_member item accumulated then accumulated
                        else accumulated @ [item]) result vars)
                    [] yes
                in
                  (quantified, used) :: no
                end
            end
        in
          make_connection connective
            (map #1 (List.foldl step groups order))
        end
      fun recurse candidate =
        if boolSyntax.is_forall candidate orelse
           boolSyntax.is_exists candidate then
          let
            val universal = boolSyntax.is_forall candidate
            val (variables, matrix) = gather universal [] candidate
            val matrix' = recurse matrix
            val connective = Option.getOpt
              (same_connective matrix', true)
            val components = connective_parts connective matrix'
            fun used component =
              List.filter (fn variable => Term.free_in variable component)
                variables
            val groups = map (fn component =>
              (component, used component, Term.term_size component))
              components
            val order =
              if length variables <= quantifier_cluster_threshold then
                best_order variables groups
              else
                greedy_order variables groups
          in
            build universal connective order
              (map (fn (component, vars, _) => (component, vars)) groups)
          end
        else if Term.is_abs candidate then
          let val (variable, body) = Term.dest_abs candidate
          in Term.mk_abs (variable, recurse body) end
        else if Term.is_comb candidate then
          let val (function, argument) = Term.dest_comb candidate
          in MFH.s_betapply (recurse function, recurse argument) end
        else
          candidate
    in
      recurse term
    end

  fun defined_free_by_assumption term =
    if boolSyntax.is_eq term then
      let val (left, right) = boolSyntax.dest_eq term
      in
        if is_user_free left andalso
           not (Term.free_in left right) then SOME left
        else NONE
      end
    else
      NONE

  fun assumption_exclusively_defines_free assumptions term =
    case defined_free_by_assumption term of
        NONE => false
      | SOME variable =>
          length (List.filter (fn assumption =>
            case defined_free_by_assumption assumption of
                SOME other => Term.aconv variable other
              | NONE => false) assumptions) = 1

  fun is_trivial_equation term =
    case Lib.total boolSyntax.dest_eq term of
        SOME (left, right) => Term.aconv left right
      | NONE => false

  fun is_constructor_pattern_formula term =
    let
      val (variables, body) = boolSyntax.strip_forall term
      val (_, conclusion) = boolSyntax.strip_imp body
      val (left, _) = boolSyntax.dest_eq conclusion
      val (_, arguments) = HolKernel.strip_comb left
    in
      List.all (is_constructor_pattern variables) arguments
    end handle HOL_ERR _ => false

  fun axioms_for_term
        (context as {user_axioms, evals, nondefs, nondef_table, ...}
          : context) assumptions negated =
    let
      val (def_assumptions, nondef_assumptions) =
        List.partition
          (assumption_exclusively_defines_free assumptions) assumptions
      val def_assumption_table = map (fn assumption =>
        (valOf (defined_free_by_assumption assumption), assumption))
        def_assumptions
      val mono_nondefs = List.filter (not o MFH.is_poly_term) nondefs
      val poly_nondefs = List.filter MFH.is_poly_term nondefs
      fun lookup_def variable = Option.map #2
        (List.find (fn (other, _) => Term.aconv variable other)
          def_assumption_table)
      fun add_axiom definitional depth axiom
            (seen, definitions, nondefinitions) =
        let
          (* FIXME: why ~1?  This exactly mirrors Nitpick's axiom-side
             skolemization depth. *)
          val normalized = axiom
            |> MFH.unfold_defs_in_term context
            |> skolemize_term_and_more context ~1
          val target = if definitional then definitions
                       else nondefinitions
        in
          if is_trivial_equation normalized orelse
             aconv_member normalized target then
            (seen, definitions, nondefinitions)
          else
            let
              val accumulator =
                if definitional then
                  (seen, normalized :: definitions, nondefinitions)
                else
                  (seen, definitions, normalized :: nondefinitions)
            in
              add_axioms_for_term (depth + 1) normalized accumulator
            end
        end
      and add_eq_axiom depth axiom accumulator =
        add_axiom (is_constructor_pattern_formula axiom)
          depth axiom accumulator
      and add_axioms_for_type _ _ accumulator = accumulator
      and add_axioms_for_term depth term
            (accumulator as (seen, definitions, nondefinitions)) =
        if Term.is_const term then
          let val already = aconv_member term seen
          in
            if already orelse MFH.is_built_in_const term then
              add_axioms_for_type depth (Term.type_of term) accumulator
            else if depth > axioms_max_depth then
              raise Refute_ModelFinder_Util.TOO_LARGE
                ("Refute_ModelFinder_Preproc.axioms_for_term",
                 "too many nested axioms")
            else
              let
                val next =
                  (term :: seen, definitions, nondefinitions)
                val with_axioms =
                  if MFH.is_constr term then
                    next
                  else if MFH.is_descr term then
                    List.foldl (fn (axiom, result) =>
                      add_axiom false depth axiom result) next
                      (MFH.equational_fun_axioms context term)
                  else if MFH.is_raw_equational_fun context term then
                    List.foldl (fn (axiom, result) =>
                      add_eq_axiom depth axiom result) next
                      (MFH.equational_fun_axioms context term)
                  else if MFH.is_choice_spec_fun context term then
                    List.foldl (fn (axiom, result) =>
                      add_axiom false depth axiom result) next
                      (MFH.choice_spec_props_for_const context term)
                  else
                    (case MFH.def_of_const context term of
                         SOME _ => List.foldl (fn (axiom, result) =>
                           add_eq_axiom depth axiom result) next
                           (MFH.equational_fun_axioms context term)
                       | NONE =>
                           if user_axioms = SOME false then next
                           else List.foldl (fn (axiom, result) =>
                             add_axiom false depth axiom result) next
                             (MFH.nondef_props_for_const nondef_table term))
              in
                add_axioms_for_type depth (Term.type_of term) with_axioms
              end
          end
        else if Term.is_var term then
          let
            val with_definition =
              if is_generated_const term orelse aconv_member term seen then
                accumulator
              else
                (case lookup_def term of
                     SOME axiom => add_axiom true depth axiom
                       (term :: seen, definitions, nondefinitions)
                   | NONE => accumulator)
          in
            add_axioms_for_type depth (Term.type_of term)
              with_definition
          end
        else if Term.is_comb term then
          let
            val (function, argument) = Term.dest_comb term
            val first = add_axioms_for_term depth function accumulator
          in
            add_axioms_for_term depth argument first
          end
        else if Term.is_abs term then
          let
            val (variable, body) = Term.dest_abs term
            val first = add_axioms_for_type depth
              (Term.type_of variable)
              (variable :: seen, definitions, nondefinitions)
          in
            add_axioms_for_term depth body first
          end
        else
          accumulator
      fun eval_axiom (serial, term) =
        boolSyntax.mk_eq
          (MFN.mk_eval serial (Term.type_of term), term)
      val eval_axioms = ListPair.zip
        (MFU.index_seq 0 (length evals), evals)
        |> map eval_axiom
      val initial = add_axioms_for_term 1 negated ([], [], [])
      val with_assumptions = List.foldr
        (fn (axiom, result) => add_axiom false 1 axiom result)
        initial nondef_assumptions
      val with_evals = List.foldr
        (fn (axiom, result) => add_axiom true 1 axiom result)
        with_assumptions eval_axioms
      val (_, definitions, selected_nondefs) =
        if user_axioms = SOME true then
          List.foldl (fn (axiom, result) =>
            add_axiom false 1 axiom result) with_evals mono_nondefs
        else
          with_evals
      val got_all_mono_user_axioms =
        user_axioms = SOME true orelse null mono_nondefs
    in
      (negated :: selected_nondefs, definitions,
       got_all_mono_user_axioms, null poly_nondefs)
    end

  fun do_tail context def destroy_constrs term =
    let
      val destroyed_sets = destroy_set_Collect term
      val pulled =
        if destroy_constrs then
          destroyed_sets
          |> pull_out_universal_constrs context def
          |> pull_out_existential_constrs context
        else
          destroyed_sets
    in
      pulled
      |> destroy_pulled_out_constrs context def destroy_constrs
      |> curry_assms
      |> destroy_universal_equalities
      |> destroy_existential_equalities
      |> simplify_constrs_and_sels context
      |> distribute_quantifiers
      |> push_quantifiers_inward
      |> close_form
    end

  fun preprocess_formulas
        (context as {destroy_constrs, ...} : context)
        assumptions negated =
    let
      val prepared = negated
        |> MFH.unfold_defs_in_term context
        |> close_form
        |> skolemize_term_and_more context max_skolem_depth
      val (nondefinitions, definitions, got_all_mono_user_axioms,
           no_poly_user_axioms) =
        axioms_for_term context assumptions prepared
      (* specialize=false, box=false, and binary_ints=false make the M3
         do_middle pass exactly the identity. *)
      val nondefinitions' = map
        (do_tail context false destroy_constrs) nondefinitions
      val definitions' = map
        (do_tail context true destroy_constrs) definitions
    in
      (nondefinitions', definitions', got_all_mono_user_axioms,
       no_poly_user_axioms)
    end
end
