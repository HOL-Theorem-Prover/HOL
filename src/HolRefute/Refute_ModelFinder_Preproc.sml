structure Refute_ModelFinder_Preproc = struct
  open Portable Feedback
  infix |>

  type term = Term.term
  type hol_type = Type.hol_type
  type context = Refute_ModelFinder_HOL.mf_context

  structure MFH = Refute_ModelFinder_HOL
  structure MFN = Refute_ModelFinder_Names
  structure Util = Refute_ModelFinder_Util

  val value_var_prefix = MFN.reserved_prefix ^ "v"
  val max_skolem_depth = 3
  val axioms_max_depth = 255
  val special_max_depth = 20
  val quantifier_cluster_threshold = 7
  val binary_int_threshold = 3

  fun err function message =
    Feedback.mk_HOL_ERR "Refute_ModelFinder_Preproc" function message

  fun variable_name variable = #1 (Term.dest_var variable)

  fun add_aconv term terms =
    if Util.aconv_member term terms then terms else terms @ [term]

  fun is_value_var term =
    case Lib.total Term.dest_var term of
        SOME (name, _) => String.isPrefix value_var_prefix name
      | NONE => false

  fun is_bound_standin term =
    case Lib.total Term.dest_var term of
        SOME (name, _) => MFN.is_bound_var_name name
      | NONE => false

  fun is_congruence_var term =
    case Lib.total Term.dest_var term of
        SOME (name, _) => MFN.is_cong_var_name name
      | NONE => false

  fun is_special_var term =
    case Lib.total Term.dest_var term of
        SOME (name, _) => MFN.is_special_name name
      | NONE => false

  fun is_schematic_var term =
    is_value_var term orelse is_bound_standin term orelse
    is_congruence_var term

  fun is_generated_const term =
    case Lib.total Term.dest_var term of
        SOME (name, _) =>
          MFN.is_reserved_name name andalso not (is_schematic_var term)
      | NONE => false

  fun is_user_free term =
    Term.is_var term andalso
    not (MFN.is_reserved_name (variable_name term))

  fun is_bound_or_value_var bound term =
    is_schematic_var term orelse Util.aconv_member term bound

  fun substitute variable replacement term =
    Term.subst [{redex = variable, residue = replacement}] term

  (* Rebuilds [candidate] with [recurse] applied to its immediate
     subterms; variables and constants are returned as they are. *)
  fun map_subterms recurse candidate =
    if Term.is_abs candidate then
      let val (variable, body) = Term.dest_abs candidate
      in Term.mk_abs (variable, recurse body) end
    else if Term.is_comb candidate then
      let val (function, argument) = Term.dest_comb candidate
      in Term.mk_comb (recurse function, recurse argument) end
    else
      candidate

  fun close_form term =
    let
      (* Isabelle's close_form closes schematic Vars, never user Frees.
         HOL4 gives each generated schematic family a reserved free name. *)
      fun closable variable = is_schematic_var variable
      fun add_frees candidate seen =
        List.foldl (fn (variable, result) =>
          if closable variable then add_aconv variable result else result)
          seen (Term.free_vars_lr candidate)
      fun close_new old current body =
        boolSyntax.list_mk_forall
          (List.drop (current, length old), body)
      fun recurse seen candidate =
        if boolSyntax.is_imp_only candidate then
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

  fun generated_or_constant_name term =
    case Lib.total Term.dest_thy_const term of
        SOME {Thy, Name, ...} => SOME (Thy ^ "$" ^ Name)
      | NONE =>
          (case Lib.total Term.dest_var term of
               SOME (name, _) =>
                 if MFN.is_reserved_name name then
                   SOME (MFN.original_name name)
                 else NONE
             | NONE => NONE)

  val binary_int_blockers =
    ["frac$abs_frac", "frac$rep_frac", "gcd$gcd", "gcd$lcm",
     "refute$nat_gcd", "refute$nat_lcm", "refute$Frac",
     "refute$norm_frac"]

  fun may_use_binary_ints definitional term =
    let
      fun blocked_constant def candidate =
        case generated_or_constant_name candidate of
            SOME name =>
              not (def andalso name = "num$SUC") andalso
              not (List.exists (fn blocker => blocker = name)
                binary_int_blockers)
          | NONE => true
      fun recurse def candidate =
        if boolSyntax.is_eq candidate then
          let val (left, right) = boolSyntax.dest_eq candidate
          in recurse def left andalso recurse false right end
        else if boolSyntax.is_imp_only candidate then
          let val (premise, conclusion) = boolSyntax.dest_imp candidate
          in recurse false premise andalso recurse def conclusion end
        else if Term.is_comb candidate then
          let val (function, argument) = Term.dest_comb candidate
          in recurse def function andalso recurse def argument end
        else if Term.is_abs candidate then
          recurse def (Term.body candidate)
        else
          blocked_constant def candidate
    in
      recurse definitional term
    end

  fun should_use_binary_ints term =
    let
      val threshold = Arbint.fromInt binary_int_threshold
      fun large_numeral candidate =
        case MFH.numeral_value candidate of
            SOME value =>
              Arbint.< (threshold, value) orelse
              Arbint.< (value, Arbint.~ threshold)
          | NONE => false
      fun integer_operation candidate =
        case Lib.total Term.dest_thy_const candidate of
            SOME {Thy, Name, ...} =>
              List.exists (fn key => key = Thy ^ "$" ^ Name)
                ["arithmetic$*", "arithmetic$DIV",
                 "integer$int_mul", "integer$int_div"] andalso
              MFH.is_integer_type
                (#2 (boolSyntax.strip_fun (Term.type_of candidate)))
          | NONE => false
      fun recurse candidate =
        large_numeral candidate orelse integer_operation candidate orelse
        if Term.is_comb candidate then
          let val (function, argument) = Term.dest_comb candidate
          in recurse function orelse recurse argument end
        else if Term.is_abs candidate then recurse (Term.body candidate)
        else false
    in
      recurse term
    end

  fun binarize_nat_and_int_in_term original =
    let
      fun int_of_numeral value =
        Arbint.toInt value
        handle Overflow =>
          raise Util.TOO_LARGE
            ("Refute_ModelFinder_Preproc.binarize_nat_and_int_in_term",
             "numeral does not fit in int")
      fun lookup variable [] = NONE
        | lookup variable ((old, replacement) :: rest) =
            if Term.aconv variable old then SOME replacement
            else lookup variable rest
      fun recurse environment candidate =
        case MFH.numeral_value candidate of
            SOME value => MFN.mk_numeral (int_of_numeral value)
              (MFH.binarize_nat_and_int_in_type (Term.type_of candidate))
          | NONE =>
              if Term.is_abs candidate then
                let
                  val (variable, body) = Term.dest_abs candidate
                  val (name, ty) = Term.dest_var variable
                  (* Retyping a binder can otherwise capture a free variable
                     with the same name at its new representation type. *)
                  val replacement = Term.variant
                    (Term.all_vars original @ map #2 environment)
                    (Term.mk_var
                      (name, MFH.binarize_nat_and_int_in_type ty))
                in
                  Term.mk_abs (replacement,
                    recurse ((variable, replacement) :: environment) body)
                end
              else if Term.is_comb candidate then
                let val (function, argument) = Term.dest_comb candidate
                in Term.mk_comb
                  (recurse environment function,
                   recurse environment argument)
                end
              else if Term.is_var candidate then
                (case lookup candidate environment of
                     SOME replacement => replacement
                   | NONE =>
                       let val (name, ty) = Term.dest_var candidate
                       in Term.mk_var (name,
                            MFH.binarize_nat_and_int_in_type ty)
                       end)
              else if Term.is_const candidate then
                MFH.retype_constant "bin" candidate
                  (MFH.binarize_nat_and_int_in_type
                    (Term.type_of candidate))
              else candidate
    in
      recurse [] original
    end

  fun is_higher_order_type ty =
    case Lib.total Type.dom_rng ty of
        SOME _ => true
      | NONE =>
          (case Lib.total Type.dest_thy_type ty of
               SOME {Args, ...} => List.exists is_higher_order_type Args
             | NONE => false)

  fun skolemize_term_with_origins prefix_origins
        (context as {skolems, ...} : context) skolem_depth term =
    let
      fun binder_origin name ty =
        let
          val matches = List.mapPartial (fn (index, (other, other_ty)) =>
            if name = other andalso Type.compare (ty, other_ty) = EQUAL then
              SOME index
            else NONE) (Lib.enumerate 0 prefix_origins)
        in
          case matches of [index] => SOME index | _ => NONE
        end
      fun positive_existential polarity existential =
        case (polarity, existential) of
            (Util.Pos, true) => true
          | (Util.Neg, false) => true
          | _ => false
      (* Keep source binder names for model display, but distinct opened
         variables for de Bruijn-style dependency identity. *)
      fun dependency_variable (variable, _, _) = variable
      fun dependency_info (variable, _, SOME origin) =
            SOME ({origin = origin, source_type = Term.type_of variable}
              : MFH.skolem_dependency)
        | dependency_info _ = NONE
      fun skolem_type dependencies result =
        boolSyntax.list_mk_fun
          (map (Term.type_of o dependency_variable) dependencies, result)
      fun recurse dependencies skolemizable polarity candidate =
        if boolSyntax.is_forall candidate orelse
           boolSyntax.is_exists candidate then
          let
            val existential = boolSyntax.is_exists candidate
            val (raw_variable, raw_body) =
              if existential then boolSyntax.dest_exists candidate
              else boolSyntax.dest_forall candidate
            val original = variable_name raw_variable
            val origin = binder_origin original (Term.type_of raw_variable)
            val occurs = Term.free_in raw_variable raw_body
            val dependency_variables = map dependency_variable dependencies
            val variable =
              if Util.aconv_member raw_variable dependency_variables then
                Term.variant (dependency_variables @ Term.all_vars raw_body)
                  raw_variable
              else
                raw_variable
            val body =
              if Term.aconv variable raw_variable then raw_body
              else substitute raw_variable variable raw_body
            fun keep () =
              let
                val transformed = recurse
                  (dependencies @ [(variable, original, origin)])
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
              recurse dependencies skolemizable polarity raw_body
            else if positive_existential polarity existential andalso
                    skolemizable andalso
                    length dependencies <= skolem_depth then
              let
                val serial = length (!skolems) + 1
                val arity = length dependencies
                val dependency_options = map dependency_info dependencies
                val dependencies_resolved =
                  List.all Option.isSome dependency_options
                val origin = if dependencies_resolved then origin else NONE
                val dependency_metadata =
                  if dependencies_resolved then map valOf dependency_options
                  else []
                val skolem = MFN.mk_skolem arity serial original
                  (skolem_type dependencies (Term.type_of variable))
                val application = Term.list_mk_comb
                  (skolem, map dependency_variable dependencies)
                val generated_name = variable_name skolem
                val info : MFH.skolem_info =
                  {origin = origin,
                   generated_name = generated_name,
                   source_name = original,
                   source_type = Term.type_of variable,
                   dependencies = dependency_metadata,
                   arity = arity,
                   stage = "source skolemization"}
                val _ = skolems :=
                  info :: !skolems
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
            (Util.flip_polarity polarity)
            (boolSyntax.dest_neg candidate))
        else if boolSyntax.is_imp_only candidate then
          let val (left, right) = boolSyntax.dest_imp candidate
          in
            boolSyntax.mk_imp
              (recurse dependencies skolemizable
                 (Util.flip_polarity polarity) left,
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
               recurse dependencies false Util.Neut argument)
          end
        else if Term.is_abs candidate then
          let val (variable, body) = Term.dest_abs candidate
          in
            Term.mk_abs (variable,
              recurse dependencies skolemizable polarity body)
          end
        else if (Term.is_const candidate orelse is_generated_const candidate)
                andalso MFH.is_raw_inductive_pred context candidate andalso
                not (MFH.is_raw_equational_fun context candidate) andalso
                not (MFH.is_well_founded_inductive_pred context candidate)
                then
          let
            val gfp = MFH.fixpoint_kind_of_const context candidate = MFH.Gfp
            fun positive () =
              recurse dependencies skolemizable polarity
                (MFH.unfold_defs_in_term context
                  (MFH.unrolled_inductive_pred_const context gfp candidate))
            fun negative () =
              MFH.fixpoint_bound_const context (not gfp) candidate
            val effective = if gfp then Util.flip_polarity polarity
              else polarity
          in
            case effective of
                Util.Pos => positive ()
              | Util.Neg => negative ()
              | Util.Neut =>
                  let
                    val (argument_tys, result_ty) = boolSyntax.strip_fun
                      (Term.type_of candidate)
                    val _ = if result_ty = Type.bool then () else
                      raise err "skolemize_term_and_more"
                        ("fixpoint constant is not a predicate: " ^
                         Parse.term_to_string candidate)
                    fun add_argument (ty, (index, avoids, arguments)) =
                      let
                        val argument = Term.variant avoids
                          (Term.mk_var ("x" ^ Int.toString index, ty))
                      in
                        (index + 1, argument :: avoids,
                         arguments @ [argument])
                      end
                    val (_, _, arguments) = List.foldl add_argument
                      (1, Term.all_vars candidate @
                          map dependency_variable dependencies, [])
                      argument_tys
                    val left = Term.list_mk_comb (positive (), arguments)
                    val right = Term.list_mk_comb (negative (), arguments)
                    val body = if gfp then boolSyntax.mk_disj (left, right)
                      else boolSyntax.mk_conj (left, right)
                  in
                    Term.list_mk_abs (arguments, body)
                  end
          end
        else
          candidate
    in
      recurse [] true Util.Pos term
    end

  fun skolemize_term_and_more
        (context as {prefix_origins, ...} : context) skolem_depth term =
    skolemize_term_with_origins (!prefix_origins) context skolem_depth term

  fun destroy_set_Collect term =
    if boolSyntax.is_IN term then
      let
        val (element, set) = boolSyntax.dest_IN term
        val transformed_element = destroy_set_Collect element
        val transformed_set = destroy_set_Collect set
      in
        if Term.is_abs transformed_set then
          destroy_set_Collect
            (Term.mk_comb (transformed_set, transformed_element))
        else
          boolSyntax.mk_IN (transformed_element, transformed_set)
      end
    else if Term.is_comb term then
      let val (function, argument) = Term.dest_comb term
      in
        Term.mk_comb
          (destroy_set_Collect function, destroy_set_Collect argument)
      end
    else if Term.is_abs term then
      let val (variable, body) = Term.dest_abs term
      in Term.mk_abs (variable, destroy_set_Collect body) end
    else
      term

  fun is_set_type ty =
    case Lib.total Type.dom_rng ty of
        SOME (_, range) => range = Type.bool
      | NONE => false

  fun heavy_variables active term =
    List.filter (fn variable =>
      is_value_var variable orelse Util.aconv_member variable active)
      (Term.free_vars_lr term)

  fun has_heavy_vars active term =
    case heavy_variables active term of
        [] => false
      | [variable] =>
          let val ty = Term.type_of variable
          in MFH.is_fun_type ty orelse is_set_type ty orelse
             MFH.is_pair_type ty
          end
      | _ => true

  fun fully_applied_constructor term =
    let
      val (head, arguments) = HolKernel.strip_comb term
    in
      if MFH.is_constr head andalso
         length arguments = length (MFH.constructor_arg_types head) then
        SOME (head, arguments)
      else
        NONE
    end

  (* With specialization disabled, keep representation boxes intact.  Pulling
     a concrete FunBox/PairBox into a low-cardinality existential can omit
     the very wrapped value required by its selector equation. *)
  fun is_function_set_or_pair preserve_boxes ty =
    MFH.is_fun_type ty orelse is_set_type ty orelse
    MFH.is_pair_type ty orelse
    preserve_boxes andalso
      (MFH.is_funbox_type ty orelse MFH.is_pairbox_type ty)

  fun fresh_value_var avoids serial ty =
    Term.variant avoids
      (MFN.mk_reserved_var
        (value_var_prefix ^ Int.toString serial) ty)

  fun pulled_lookup term pulled =
    Option.map #2 (List.find (fn (other, _) => Term.aconv other term)
      pulled)

  fun pull_candidate preserve_boxes avoids active forbidden relax
        candidate pulled =
    case fully_applied_constructor candidate of
        NONE => (candidate, pulled)
      | SOME _ =>
          if relax orelse
             is_function_set_or_pair preserve_boxes (Term.type_of candidate)
             orelse not (has_heavy_vars active candidate) orelse
             List.exists (fn variable => Term.free_in variable candidate)
               forbidden then
            (candidate, pulled)
          else
            (case pulled_lookup candidate pulled of
                 SOME variable => (variable, pulled)
               | NONE =>
                   let
                     val variable = fresh_value_var
                       (avoids @ map #2 pulled) (length pulled + 1)
                       (Term.type_of candidate)
                   in
                     (variable, (candidate, variable) :: pulled)
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
              if relaxed then (right, pulled)
              else recurse forbidden false right pulled
            val (left', pulled'') =
              recurse forbidden false left pulled'
          in
            (boolSyntax.mk_eq (left', right'), pulled'')
          end
        else if boolSyntax.is_imp_only candidate then
          let
            (* HOL4 has only object implication here.  Nitpick resets the
               definition flag on both sides of object implication; only
               Isabelle's separate Pure.imp keeps a definition body opaque. *)
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
            fun do_arguments [] current = ([], current)
              | do_arguments (argument :: rest) current =
                  let
                    (* Application descent in Nitpick visits the rightmost
                       argument first.  Preserve that order because it fixes
                       value-variable serials and premise order. *)
                    val (rest', current') = do_arguments rest current
                    val (argument', current'') =
                      recurse forbidden relaxed argument current'
                  in
                    (argument' :: rest', current'')
                  end
            val (arguments', pulled') =
              do_arguments arguments pulled
            val (head', pulled'') =
              recurse forbidden relaxed head pulled'
            val rebuilt = Term.list_mk_comb (head', arguments')
          in
            pull_candidate (not (#specialize context)) avoids [] forbidden
              relaxed rebuilt pulled''
          end
        else
          pull_candidate (not (#specialize context)) avoids [] forbidden
            relaxed candidate pulled
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
      fun recurse outer existentials candidate =
        if boolSyntax.is_exists candidate then
          let
            val (variable, body) = boolSyntax.dest_exists candidate
            val active = existentials @ [variable]
            val (body', pulled) = collect outer active body []
            val equations = equations_for_pulled pulled
            val fresh = map #2 pulled
            val matrix = List.foldl (fn (equation, result) =>
              smart_conj [equation, result]) body' equations
          in
            boolSyntax.mk_exists (variable,
              boolSyntax.list_mk_exists (rev fresh, matrix))
          end
        else if boolSyntax.is_forall candidate then
          let val (variable, body) = boolSyntax.dest_forall candidate
          in boolSyntax.mk_forall (variable,
               recurse (existentials @ variable :: outer) [] body)
          end
        else if Term.is_abs candidate then
          let val (variable, body) = Term.dest_abs candidate
          in Term.mk_abs (variable,
               recurse (existentials @ variable :: outer) [] body) end
        else if Term.is_comb candidate then
          let val (function, argument) = Term.dest_comb candidate
          in Term.mk_comb (recurse outer existentials function,
               recurse outer existentials argument) end
        else
          candidate
      and collect outer existentials candidate pulled =
        if boolSyntax.is_exists candidate then
          (recurse outer existentials candidate, pulled)
        else if Term.is_abs candidate then
          let val (variable, body) = Term.dest_abs candidate
          in
            (Term.mk_abs (variable,
               recurse (existentials @ variable :: outer) [] body),
             pulled)
          end
        else if Term.is_comb candidate then
          let
            val (head, arguments) = HolKernel.strip_comb candidate
            fun do_arguments [] current = ([], current)
              | do_arguments (argument :: rest) current =
                  let
                    val (rest', current') = do_arguments rest current
                    val (argument', current'') =
                      collect outer existentials argument current'
                  in
                    (argument' :: rest', current'')
                  end
            val (arguments', pulled') =
              do_arguments arguments pulled
            val (head', pulled'') =
              collect outer existentials head pulled'
            val rebuilt = Term.list_mk_comb (head', arguments')
          in
            pull_candidate (not (#specialize context)) avoids existentials
              outer false rebuilt pulled''
          end
        else
          pull_candidate (not (#specialize context)) avoids existentials
            outer false candidate pulled
    in
      recurse [] [] term
    end

  (* Shared with the monotonicity calculus, which passes a wider leaf
     test; see Refute_ModelFinder_HOL.is_constructor_pattern_gen. *)
  val is_constructor_pattern =
    MFH.is_constructor_pattern_gen is_bound_or_value_var

  (* Pulled-out values are represented by free reserved variables in HOL4.
     Count only their free occurrences: a same-named abstraction binder is
     alpha-local and must neither be collected nor affect this count. *)
  fun count_free_occurrences needle term =
    let
      val here = if Term.aconv needle term then 1 else 0
    in
      if Term.is_comb term then
        let val (function, argument) = Term.dest_comb term
        in here + count_free_occurrences needle function +
           count_free_occurrences needle argument
        end
      else if Term.is_abs term then
        let val (variable, body) = Term.dest_abs term
        in
          if Term.aconv needle variable then 0
          else count_free_occurrences needle body
        end
      else
        here
    end

  fun destructible_constructor term =
    let
      val (head, arguments) = HolKernel.strip_comb term
      val constructor =
        MFH.is_constr head orelse MFH.is_pair_constructor head orelse
        MFH.is_suc_constructor head
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
            is_value_var variable orelse Util.aconv_member variable bound)
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
        if boolSyntax.is_imp_only candidate then
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
            Term.mk_comb
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
                not (Util.aconv_member right bound) andalso
                count_free_occurrences right term = 1 then
          boolSyntax.T
        else
          case destructible_constructor right of
              SOME (constructor, arguments) =>
                let
                  val argument_tys =
                    MFH.constructor_arg_types constructor
                  val indexed = ListPair.zip
                    (Util.index_seq 0 (length arguments),
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
    if boolSyntax.is_imp_only term then
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
        if boolSyntax.is_imp_only candidate then
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
                    SOME (replacement, rest @ seen)
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
          (* Nitpick's conjuncts_of traverses the right branch first. *)
          kill variables (rev (boolSyntax.strip_conj (recurse matrix)))
        end
      and recurse candidate =
        if boolSyntax.is_exists candidate then
          let val (variables, matrix) = boolSyntax.strip_exists candidate
          in process_cluster variables matrix end
        else
          map_subterms recurse candidate
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
                 if MFH.is_free_constr constructor andalso
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
      (* This pass recognizes selector reconstruction only.  The general
         construct_value helper also eta-contracts unrelated arguments. *)
      fun reconstruct constructor arguments =
        case arguments of
            [] => NONE
          | first :: _ =>
              (case MFH.generated_selector_argument constructor first of
                   SOME value =>
                     if Term.type_of value <>
                        MFH.constructor_result_type constructor then
                       NONE
                     else
                       let
                         val argument_tys =
                           MFH.constructor_arg_types constructor
                         val expected = List.tabulate
                           (length argument_tys, fn index =>
                             MFH.select_nth_constr_arg context constructor
                               value index
                               (List.nth (argument_tys, index)))
                       in
                         if ListPair.allEq (fn (left, right) =>
                              Term.aconv left right)
                              (arguments, expected) then
                           SOME value
                         else
                           NONE
                       end
                 | NONE => NONE)
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
            if MFH.is_nonfree_constr head' andalso
               length arguments' =
                 length (MFH.constructor_arg_types head') then
              Option.getOpt
                (reconstruct head' arguments', rebuilt)
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
        else if boolSyntax.is_imp_only body then
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
      in Term.mk_comb
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
      fun gather_rev universal variables candidate =
        if (universal andalso boolSyntax.is_forall candidate) orelse
           (not universal andalso boolSyntax.is_exists candidate) then
          let
            val (raw_variable, raw_body) =
              if universal then boolSyntax.dest_forall candidate
              else boolSyntax.dest_exists candidate
          in
            if not (Term.is_comb raw_body) then
              (variables, candidate)
            else
              let
                val duplicate = Util.aconv_member raw_variable variables
                val variable =
                  if duplicate then
                    Term.variant (variables @ Term.free_vars_lr raw_body)
                      raw_variable
                  else
                    raw_variable
                val body =
                  if duplicate then substitute raw_variable variable raw_body
                  else raw_body
              in
                gather_rev universal (variable :: variables) body
              end
          end
        else
          (variables, candidate)
      (* Accumulating innermost-first costs no append per binder; the
         cluster is read outermost-first, so reverse once at the end. *)
      fun gather universal candidate =
        let val (variables, matrix) = gather_rev universal [] candidate
        in (rev variables, matrix) end
      fun merge_groups variable_cost variable groups =
        let
          val (yes, no) = List.partition
            (fn (_, used, _) => Util.aconv_member variable used) groups
        in
          if null yes then no
          else
            let
              val used = List.foldl
                (fn ((_, vars, _), result) =>
                  List.foldl (fn (item, accumulated) =>
                    if Util.aconv_member item accumulated then accumulated
                    else accumulated @ [item]) result vars)
                [] yes
              val size = List.foldl
                (fn ((_, _, cost), total) => total + cost)
                (0 : IntInf.int) yes *
                IntInf.fromInt (variable_cost variable)
            in
              (boolSyntax.T, used, size) :: no
            end
        end
      fun groups_cost groups =
        List.foldl (fn ((_, _, cost), total) => total + cost)
          (0 : IntInf.int) groups
      fun merge_in_order variable_cost order groups =
        List.foldl (fn (variable, current) =>
          merge_groups variable_cost variable current) groups order
      fun best_order variable_cost variables groups =
        let
          fun cost order = groups_cost
            (merge_in_order variable_cost order groups)
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
            (Util.all_permutations variables)))
        end
      fun greedy_order _ [] _ = []
        | greedy_order variable_cost variables groups =
            let
              fun remove chosen = List.filter
                (fn variable => not (Term.aconv chosen variable))
                  variables
              fun choose (variable, NONE) =
                    SOME (groups_cost
                      (merge_groups variable_cost variable groups), variable)
                | choose (variable,
                    SOME (best as (best_cost, _))) =
                    let
                      val candidate_cost = groups_cost
                        (merge_groups variable_cost variable groups)
                    in
                      if candidate_cost < best_cost then
                        SOME (candidate_cost, variable)
                      else
                        SOME best
                    end
              val chosen = #2 (valOf
                (List.foldl choose NONE variables))
            in
              chosen :: greedy_order variable_cost (remove chosen)
                (merge_groups variable_cost chosen groups)
            end
      fun build universal connective order groups =
        let
          fun step (variable, current) =
            let
              val (yes, no) = List.partition
                (fn (_, used) => Util.aconv_member variable used) current
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
                        if Util.aconv_member item accumulated then accumulated
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
            val (variables, matrix) = gather universal candidate
            (* Match Nitpick: the current cluster treats its matrix as
               opaque.  Structural recursion resumes outside the cluster. *)
            val connective = Option.getOpt
              (same_connective matrix, true)
            val components = connective_parts connective matrix
            fun used component =
              List.filter (fn variable => Term.free_in variable component)
                variables
            val groups = map (fn component =>
              (component, used component,
               IntInf.fromInt (Term.term_size component))) components
            (* Precomputed: the permutation search asks n! * n times.
               Nitpick keeps this table innermost-first but indexes it by
               the outermost-first bound number, charging each binder its
               mirror's cardinality; that mis-orders a cluster whose types
               differ in size, so index it directly instead. *)
            val variable_cards =
              map (MFH.typical_card_of_type o Term.type_of) variables
            fun variable_cost variable =
              List.nth (variable_cards,
                Lib.index (fn other => Term.aconv variable other) variables)
            val order =
              if length variables <= quantifier_cluster_threshold then
                best_order variable_cost variables groups
              else
                greedy_order variable_cost variables groups
          in
            build universal connective order
              (map (fn (component, vars, _) => (component, vars)) groups)
          end
        else
          map_subterms recurse candidate
    in
      recurse term
    end

  (** Function specialization **)

  fun function_name term =
    case Lib.total Term.dest_thy_const term of
        SOME {Thy, Name, ...} => Thy ^ MFN.name_sep ^ Name
      | NONE => #1 (Term.dest_var term)

  fun same_function left right =
    Term.aconv left right orelse
    (Term.is_const left andalso Term.is_const right andalso
     Term.same_const left right andalso Term.type_of left = Term.type_of right)

  fun params_in_equation term =
    let
      val (_, body) = boolSyntax.strip_forall term
      val (_, conclusion) = boolSyntax.strip_imp body
      val (left, _) = boolSyntax.dest_eq conclusion
    in
      #2 (HolKernel.strip_comb left)
    end handle HOL_ERR _ => []

  fun schematic_vars_in terms =
    let
      fun add (variable, result) =
        if is_schematic_var variable andalso
           not (Util.aconv_member variable result) then
          variable :: result
        else
          result
      val variables = List.concat (map Term.free_vars_lr terms)
    in
      Listsort.sort Term.compare (List.foldl add [] variables)
    end

  fun schematize_foralls avoids axiom =
    let
      val (variables, body) = boolSyntax.strip_forall axiom
      fun make (variable, (serial, used, substitutions)) =
        let
          val fresh = fresh_value_var used serial (Term.type_of variable)
        in
          (serial + 1, fresh :: used,
           {redex = variable, residue = fresh} :: substitutions)
        end
      val (_, _, substitutions) = List.foldl make
        (1, List.concat (map Term.all_vars avoids) @ Term.all_vars axiom,
         []) variables
    in
      Term.subst (rev substitutions) body
    end

  fun specialize_fun_axiom original special fixed_indices fixed_args
        extra_args axiom =
    let
      val raw_body = schematize_foralls (fixed_args @ extra_args) axiom
      val fixed_params = Util.filter_indices fixed_indices
        (params_in_equation raw_body)
      val body = Term.subst
        (ListPair.map (fn (parameter, argument) =>
          {redex = parameter, residue = argument})
          (fixed_params, fixed_args)) raw_body
      fun recurse arguments candidate =
        if Term.is_comb candidate then
          let val (function, argument) = Term.dest_comb candidate
          in recurse (recurse [] argument :: arguments) function end
        else if Term.is_abs candidate then
          let val (variable, abs_body) = Term.dest_abs candidate
          in
            Term.list_mk_comb
              (Term.mk_abs (variable, recurse [] abs_body), arguments)
          end
        else if same_function candidate original then
          Term.list_mk_comb
            (special, extra_args @
              Util.filter_out_indices fixed_indices arguments)
        else
          Term.list_mk_comb (candidate, arguments)
    in
      recurse [] body
    end

  fun is_ersatz_call ({ersatz_table, ...} : context) original candidate =
    if not (Term.is_const candidate) then false
    else
      let
        val original_key = MFH.const_key original
        val candidate_key = MFH.const_key candidate
      in
        List.exists (fn ({original = source, replacement} : MFH.ersatz) =>
          MFH.same_key source original_key andalso
          MFH.same_key replacement candidate_key andalso
          Term.type_of original = Term.type_of candidate) ersatz_table
      end handle HOL_ERR _ => false

  fun static_args_in_term context original term =
    let
      val (formal_variables, matrix) = boolSyntax.strip_forall term
      fun is_formal variable = Util.aconv_member variable formal_variables
      (* [Term.dest_abs] frees a binder under its own name, so one shadowing
         a formal is aconv to it where Isabelle would see a Bound.  Keep the
         binders in scope with each call and never call an argument they
         reach static: dropping it would fix the binder's value to the one
         the call site passes. *)
      fun calls bound candidate arguments result =
        if Term.is_abs candidate then
          let val (variable, body) = Term.dest_abs candidate
          in calls (variable :: bound) body [] result end
        else if Term.is_comb candidate then
          let val (function, argument) = Term.dest_comb candidate
              val after_argument = calls bound argument [] result
          in calls bound function (argument :: arguments) after_argument end
        else if same_function candidate original orelse
                is_ersatz_call context original candidate then
          (bound, arguments) :: result
        else
          result
      val call_sites = calls [] matrix [] []
      fun applied index =
        List.all (fn (_, arguments) => index < length arguments) call_sites
      fun terms_at index =
        if applied index then
          map (fn (_, arguments) => List.nth (arguments, index)) call_sites
        else
          []
      fun locally_bound_at index =
        applied index andalso
        List.exists (fn (bound, arguments) =>
          List.exists (fn variable =>
            Term.free_in variable (List.nth (arguments, index))) bound)
          call_sites
      val maximum = List.foldl Int.max 0
        (map (fn (_, arguments) => length arguments) call_sites)
      val sets = List.tabulate (maximum, fn index =>
        Util.distinct_terms (terms_at index))
      fun first_equal singleton =
        Lib.index (fn terms =>
          length terms = 1 andalso Term.aconv (hd terms) singleton) sets
      fun classify (index, [singleton]) =
            if locally_bound_at index then NONE
            else if Term.is_var singleton andalso is_formal singleton then
              if first_equal singleton = index then SOME (index, NONE)
              else NONE
            else if Term.is_const singleton orelse
                    (Term.is_var singleton andalso
                     not (is_schematic_var singleton)) then
              SOME (index, SOME singleton)
            else
              NONE
        | classify _ = NONE
    in
      if null call_sites then []
      else List.mapPartial classify
        (ListPair.zip (Util.index_seq 0 (length sets), sets))
    end

  fun same_static ((left_index, left_term),
                   (right_index, right_term)) =
    left_index = right_index andalso
    case (left_term, right_term) of
        (NONE, NONE) => true
      | (SOME left, SOME right) => Term.aconv left right
      | _ => false

  fun static_args_in_terms context original axioms =
    case map (static_args_in_term context original) axioms of
        [] => []
      | first :: rest => List.foldl (fn (current, result) =>
          List.filter (fn parameter =>
            List.exists (fn other => same_static (parameter, other)) current)
            result) first rest

  fun is_special_eligible_arg bound argument =
    let
      val schematic = schematic_vars_in [argument]
      val enclosing = List.filter (fn variable =>
        Term.free_in variable argument) bound
      val bad = schematic @ List.filter (fn variable =>
        not (Util.aconv_member variable schematic)) enclosing
      val product = List.foldl (fn (variable, result) =>
        result * IntInf.fromInt
          (MFH.typical_card_of_type (Term.type_of variable)))
        (1 : IntInf.int) bad
    in
      null bad orelse
      product < IntInf.fromInt
        (MFH.typical_card_of_type (Term.type_of argument))
    end

  fun overlapping_indices static eligible actual_args =
    List.mapPartial (fn (index, fixed) =>
      if not (List.exists (fn eligible_index =>
           eligible_index = index) eligible) then
        NONE
      else
        case fixed of
            NONE => SOME index
          | SOME literal =>
              if index < length actual_args andalso
                 Term.aconv literal (List.nth (actual_args, index)) then
                SOME index
              else
                NONE) static

  fun special_fun_aconv
        ((original1, indices1, arguments1),
         (original2, indices2, arguments2)) =
    same_function original1 original2 andalso indices1 = indices2 andalso
    length arguments1 = length arguments2 andalso
    ListPair.allEq (fn (left, right) => Term.aconv left right)
      (arguments1, arguments2)

  fun special_cache_lookup entries key =
    Option.map #2 (List.find (fn (stored, _) =>
      special_fun_aconv (stored, key)) entries)

  fun specialize_consts_in_term
        (context as {specialize, special_funs, simp_table, ...} : context)
        definitional depth term =
    if not specialize orelse depth > special_max_depth then term
    else
      let
        val blacklist =
          if definitional then [MFH.term_under_def term] else []
        fun blacklisted original =
          List.exists (same_function original) blacklist
        fun eligible_candidate original arguments =
          Term.is_const original andalso not (null arguments) andalso
          not (blacklisted original) andalso
          not (MFN.is_special_name (function_name original)) andalso
          not (MFH.is_built_in_const original) andalso
          not (MFH.is_constr original) andalso
          not (MFH.is_choice_spec_fun context original) andalso
          (MFH.is_equational_fun context original orelse
           Option.isSome (MFH.def_of_const context original))
        fun replace_bound selected standins candidate =
          List.foldl (fn ((variable, standin), result) =>
            substitute variable standin result) candidate
            (ListPair.zip (selected, standins))
        fun specialize_occurrence bound original arguments =
          let
            val _ =
              if MFH.is_raw_inductive_pred context original then
                case MFH.fixpoint_refusal_reason context original of
                    SOME reason =>
                      raise Refute_ModelFinder_Util.NOT_SUPPORTED reason
                  | NONE => ()
              else ()
          in
          if not (eligible_candidate original arguments) then
            Term.list_mk_comb (original, arguments)
          else
            let
              val eligible = List.mapPartial (fn (index, argument) =>
                if is_special_eligible_arg bound argument then SOME index
                else NONE)
                (ListPair.zip
                  (Util.index_seq 0 (length arguments), arguments))
              val old_axioms = map destroy_existential_equalities
                (MFH.equational_fun_axioms context original)
              val static = static_args_in_terms context original old_axioms
              val fixed_indices =
                overlapping_indices static eligible arguments
            in
              if null eligible orelse null fixed_indices then
                Term.list_mk_comb (original, arguments)
              else
                let
                  val fixed_args =
                    Util.filter_indices fixed_indices arguments
                  val selected_bounds = List.filter (fn variable =>
                    List.exists (Term.free_in variable) fixed_args) bound
                  fun make_standin
                        (variable, (index, used, result)) =
                    let
                      fun collides candidate = List.exists (fn other =>
                        variable_name candidate = variable_name other) used
                      fun choose serial =
                        let val candidate = MFN.mk_bound_var serial
                          (Term.type_of variable)
                        in
                          if collides candidate then choose (serial + 1)
                          else (serial, candidate)
                        end
                      val (serial, fresh) = choose (index + 1)
                    in
                      (serial, fresh :: used, result @ [fresh])
                    end
                  val (_, _, standins) = List.foldl make_standin
                    (0, List.concat (map Term.all_vars fixed_args), [])
                    selected_bounds
                  val fixed_args_in_axiom = map
                    (replace_bound selected_bounds standins) fixed_args
                  val axiom_bounds = schematic_vars_in fixed_args_in_axiom
                  fun actual_bound schematic =
                    case List.find (fn (standin, _) =>
                           Term.aconv schematic standin)
                           (ListPair.zip (standins, selected_bounds)) of
                        SOME (_, actual) => actual
                      | NONE => schematic
                  val actual_bounds = map actual_bound axiom_bounds
                  val live_args =
                    Util.filter_out_indices fixed_indices arguments
                  val extra_args = actual_bounds @ live_args
                  val extra_types = map Term.type_of axiom_bounds
                  val (binder_types, body_type) =
                    boolSyntax.strip_fun (Term.type_of original)
                  val special_type = boolSyntax.list_mk_fun
                    (extra_types @
                     Util.filter_out_indices fixed_indices binder_types,
                     body_type)
                  val key =
                    (original, fixed_indices, fixed_args_in_axiom)
                in
                  case special_cache_lookup (!special_funs) key of
                      SOME special =>
                        Term.list_mk_comb (special, extra_args)
                    | NONE =>
                        let
                          val special = MFN.mk_special
                            (length (!special_funs) + 1)
                            (function_name original) special_type
                          val axiom_extra_args = axiom_bounds
                          val new_axioms = map
                            (specialize_fun_axiom original special
                              fixed_indices fixed_args_in_axiom
                              axiom_extra_args) old_axioms
                          val _ = special_funs :=
                            (key, special) :: !special_funs
                          val _ = MFH.add_simps simp_table special new_axioms
                        in
                          Term.list_mk_comb (special, extra_args)
                        end
                end
            end
          end
        fun recurse bound candidate =
          if Term.is_abs candidate then
            let
              val (variable, raw_body) = Term.dest_abs candidate
              (* Bound-variable identity is represented by a HOL term below.
                 Alpha-rename a shadowing binder before adding it to that
                 environment, so selected_bounds cannot conflate its outer
                 namesake with this local binding. *)
              val (variable, body) =
                if List.exists (Term.aconv variable) bound then
                  let val fresh = Term.variant
                    (bound @ Term.all_vars raw_body) variable
                  in (fresh, substitute variable fresh raw_body) end
                else
                  (variable, raw_body)
            in
              Term.mk_abs (variable, recurse (bound @ [variable]) body)
            end
          else if Term.is_comb candidate then
            let
              val (head, arguments) = HolKernel.strip_comb candidate
              val arguments' = map (recurse bound) arguments
            in
              if Term.is_const head then
                specialize_occurrence bound head arguments'
              else
                Term.list_mk_comb (recurse bound head, arguments')
            end
          else
            candidate
      in
        recurse [] term
      end

  type special_triple = int list * term list * term

  fun fixed_lookup index (indices, terms, _) =
    let
      fun find [] [] = NONE
        | find (current :: rest_indices) (term :: rest_terms) =
            if current = index then SOME term
            else find rest_indices rest_terms
        | find _ _ = NONE
    in
      find indices terms
    end

  fun special_congruence_axiom original_type
        (first as (_, first_terms, first_special) : special_triple)
        (second as (_, second_terms, second_special) : special_triple) =
    let
      val first_bounds = schematic_vars_in first_terms
      val second_bounds = schematic_vars_in second_terms
      val (argument_types, _) = boolSyntax.strip_fun original_type
      val maximum = List.foldl Int.max (~1)
        (#1 first @ #1 second)
      fun step (index, (premises, first_args, second_args)) =
        case (fixed_lookup index first, fixed_lookup index second) of
            (SOME left, SOME right) =>
              if Term.aconv left right then
                (premises, first_args, second_args)
              else
                (add_aconv (boolSyntax.mk_eq (left, right)) premises,
                 first_args, second_args)
          | (SOME left, NONE) =>
              (premises, first_args, second_args @ [left])
          | (NONE, SOME right) =>
              (premises, first_args @ [right], second_args)
          | (NONE, NONE) =>
              let
                val variable = MFN.mk_cong_var index
                  (List.nth (argument_types, index))
              in
                (premises, first_args @ [variable],
                 second_args @ [variable])
              end
      val (premises, first_args, second_args) = List.foldl step
        ([], [], []) (Util.index_seq 0 (maximum + 1))
      val conclusion = boolSyntax.mk_eq
        (Term.list_mk_comb
           (first_special, first_bounds @ first_args),
         Term.list_mk_comb
           (second_special, second_bounds @ second_args))
    in
      boolSyntax.list_mk_imp (premises, conclusion)
    end

  fun special_congruence_axioms
        (context as {special_funs, ...} : context) seen =
    let
      fun add_group (((original, indices, terms), special), groups) =
        case List.find (fn (other, _) => same_function original other)
               groups of
            NONE => (original, [(indices, terms, special)]) :: groups
          | SOME (_, triples) =>
              (original, (indices, terms, special) :: triples) ::
              List.filter (fn (other, _) =>
                not (same_function original other)) groups
      val raw_groups = List.foldl add_group [] (!special_funs)
      val groups = List.mapPartial (fn (original, triples) =>
        if MFH.is_equational_fun_surely_complete context original then NONE
        else
          SOME (original,
            if HOLset.member (seen, original) then
              ([], [], original) :: triples
            else triples)) raw_groups
      fun pair_subset (small_indices, small_terms)
            (large_indices, large_terms) =
        List.all (fn (index, term) =>
          case fixed_lookup index
            (large_indices, large_terms, boolSyntax.T) of
              SOME other => Term.aconv term other
            | NONE => false)
          (ListPair.zip (small_indices, small_terms))
      fun more_specific
            ((indices1, terms1, special1) : special_triple)
            ((indices2, terms2, special2) : special_triple) =
        not (Term.aconv special1 special2) andalso
        length indices2 < length indices1 andalso
        pair_subset (indices2, terms2) (indices1, terms1)
      fun compare_generality ((indices1, _, _), (indices2, _, _)) =
        Int.compare (length indices2, length indices1)
      fun pass1 original triples =
        let
          fun visit (triple, (axioms, skipped)) =
            case Listsort.sort compare_generality
              (List.filter (more_specific triple) triples) of
                general :: _ =>
                  (special_congruence_axiom (Term.type_of original)
                     triple general :: axioms, skipped)
              | [] => (axioms, triple :: skipped)
          val (axioms, skipped) = List.foldl visit ([], []) triples
          fun pairs [] result = result
            | pairs (triple :: rest) result =
                pairs rest (List.foldl (fn (other, current) =>
                  special_congruence_axiom (Term.type_of original)
                    triple other :: current) result rest)
        in
          pairs skipped axioms
        end
    in
      List.concat (map (fn (original, triples) =>
        pass1 original triples) groups)
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

  val is_constructor_pattern_formula =
    MFH.is_constructor_pattern_formula_gen is_bound_or_value_var

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
      (* Term.compare is alpha-invariant (src/0/Term.sml: the Abs case
         compares binder types and de Bruijn bodies only), so these HOLsets
         decide exactly what the old linear Term.aconv scans decided.  The
         lists stay for output order; the sets carry the membership tests. *)
      val no_terms = HOLset.empty Term.compare
      fun add_axiom definitional depth axiom
            (seen, definitions, def_set, nondefinitions, nondef_set) =
        let
          (* FIXME: why ~1?  This exactly mirrors Nitpick's axiom-side
             skolemization depth. *)
          val base = axiom
            |> MFH.unfold_defs_in_term context
            |> skolemize_term_with_origins [] context ~1
          val target = if definitional then def_set else nondef_set
        in
          if is_trivial_equation base orelse HOLset.member (target, base) then
            (seen, definitions, def_set, nondefinitions, nondef_set)
          else
            let
              val normalized = specialize_consts_in_term context
                definitional depth base
            in
              if HOLset.member (target, normalized) then
                (seen, definitions, def_set, nondefinitions, nondef_set)
              else
                let
                  val accumulator =
                    if definitional then
                      (seen, normalized :: definitions,
                       HOLset.add (def_set, normalized),
                       nondefinitions, nondef_set)
                    else
                      (seen, definitions, def_set,
                       normalized :: nondefinitions,
                       HOLset.add (nondef_set, normalized))
                in
                  add_axioms_for_term (depth + 1) [] normalized accumulator
                end
            end
        end
      and add_eq_axiom depth axiom accumulator =
        add_axiom (is_constructor_pattern_formula axiom)
          depth axiom accumulator
      and add_maybe_def_axiom depth axiom accumulator =
        let val (_, body) = boolSyntax.strip_forall axiom
        in
          add_axiom (not (boolSyntax.is_imp_only body))
            depth axiom accumulator
        end
      and add_axioms_for_type depth ty accumulator =
        let
          val arguments =
            if Type.is_vartype ty then []
            else #Args (Type.dest_thy_type ty)
          val with_arguments = List.foldl
            (fn (argument, result) =>
              add_axioms_for_type depth argument result)
            accumulator arguments
        in
          if #max_bisim_depth context >= 0 andalso
             MFH.is_codatatype ty then
            (* These axioms define the finite bisimulation support itself.
               Treating their codatatype quantifiers as ordinary nondefs
               adds an unrepresented-value guard and makes every sound
               scope false before the support relation can constrain it. *)
            List.foldl (fn (axiom, result) =>
              add_axiom true depth axiom result) with_arguments
              (MFH.codatatype_bisim_axioms context ty)
          else if MFH.is_quot_type ty then
            List.foldl (fn (axiom, result) =>
              add_axiom true depth axiom result) with_arguments
              (MFH.optimized_quot_type_axioms context ty)
          else if MFH.is_typedef ty then
            let
              val with_membership = List.foldl (fn (axiom, result) =>
                add_maybe_def_axiom depth axiom result) with_arguments
                (MFH.optimized_typedef_axioms ty)
            in
              case MFH.typedef_for_type ty of
                  SOME {rep, ...} => List.foldl (fn (axiom, result) =>
                    add_axiom true depth axiom result) with_membership
                    (MFH.optimized_inverse_axioms_for_rep_fun rep)
                | NONE => with_membership
            end
          else
            with_arguments
        end
      and add_axioms_for_term depth bound term
            (accumulator as
               (seen, definitions, def_set, nondefinitions, nondef_set)) =
        if Term.is_const term orelse is_special_var term orelse
           is_generated_const term then
          let val already = HOLset.member (seen, term)
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
                  (HOLset.add (seen, term), definitions, def_set,
                   nondefinitions, nondef_set)
                val with_axioms =
                  if MFH.is_rep_fun term then
                    let
                      val with_inverses = List.foldl
                        (fn (axiom, result) =>
                          add_axiom true depth axiom result) next
                        (MFH.optimized_inverse_axioms_for_rep_fun term)
                    in
                      add_axioms_for_term depth []
                        (MFH.mate_of_rep_fun term) with_inverses
                    end
                  else if MFH.is_constr term then
                    next
                  else if MFH.is_descr term then
                    List.foldl (fn (axiom, result) =>
                      add_axiom false depth axiom result) next
                      (MFH.equational_fun_axioms context term)
                  else if MFH.is_raw_inductive_pred context term then
                    (case MFH.fixpoint_refusal_reason context term of
                         SOME reason =>
                           raise Refute_ModelFinder_Util.NOT_SUPPORTED reason
                       | NONE => List.foldl (fn (axiom, result) =>
                           add_eq_axiom depth axiom result) next
                           (MFH.equational_fun_axioms context term))
                  else if MFH.is_fixpoint_bound_const term orelse
                          MFH.is_raw_equational_fun context term then
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
              if Util.aconv_member term bound orelse
                 is_generated_const term orelse
                 HOLset.member (seen, term) then
                accumulator
              else
                (case lookup_def term of
                     SOME axiom => add_axiom true depth axiom
                       (HOLset.add (seen, term), definitions, def_set,
                        nondefinitions, nondef_set)
                   | NONE => accumulator)
          in
            add_axioms_for_type depth (Term.type_of term)
              with_definition
          end
        else if Term.is_comb term then
          let
            val (function, argument) = Term.dest_comb term
            val first = add_axioms_for_term depth bound function accumulator
          in
            add_axioms_for_term depth bound argument first
          end
        else if Term.is_abs term then
          let
            val (variable, body) = Term.dest_abs term
            val first = add_axioms_for_term depth (variable :: bound)
              body accumulator
          in
            add_axioms_for_type depth (Term.type_of variable) first
          end
        else
          accumulator
      fun eval_axiom (serial, term) =
        boolSyntax.mk_eq
          (MFN.mk_eval serial (Term.type_of term), term)
      val eval_axioms = ListPair.zip
        (Util.index_seq 0 (length evals), evals)
        |> map eval_axiom
      val initial = add_axioms_for_term 1 [] negated
        (no_terms, [], no_terms, [], no_terms)
      val with_assumptions = List.foldr
        (fn (axiom, result) => add_axiom false 1 axiom result)
        initial nondef_assumptions
      val with_evals = List.foldr
        (fn (axiom, result) => add_axiom true 1 axiom result)
        with_assumptions eval_axioms
      val (final_seen, definitions, _, selected_nondefs, _) =
        if user_axioms = SOME true then
          List.foldl (fn (axiom, result) =>
            add_axiom false 1 axiom result) with_evals mono_nondefs
        else
          with_evals
      val congruence_axioms =
        special_congruence_axioms context final_seen
      val got_all_mono_user_axioms =
        user_axioms = SOME true orelse null mono_nondefs
    in
      (negated :: selected_nondefs, definitions @ congruence_axioms,
       got_all_mono_user_axioms, null poly_nondefs)
    end

  fun uncurry_prefix_for count prefix =
    MFN.uncurry_prefix ^ Int.toString count ^ "@" ^
    Int.toString prefix ^ MFN.name_sep

  fun uncurry_name term =
    case Lib.total Term.dest_thy_const term of
        SOME {Thy, Name, ...} => Thy ^ MFN.name_sep ^ Name
      | NONE => #1 (Term.dest_var term)

  fun add_to_uncurry_table context term table =
    let
      fun update constant arity entries =
        case List.find (Term.aconv constant o #1) entries of
            NONE => (constant, arity) :: entries
          | SOME (_, old) =>
              (constant, Int.min (old, arity)) ::
              List.filter (not o Term.aconv constant o #1) entries
      fun skippable candidate =
        MFH.is_built_in_const candidate orelse
        MFH.is_nonfree_constr candidate orelse
        MFN.is_sel (uncurry_name candidate)
      fun recurse candidate arguments entries =
        if Term.is_comb candidate then
          let
            val (function, argument) = Term.dest_comb candidate
            val entries = recurse argument [] entries
          in recurse function (argument :: arguments) entries end
        else if Term.is_abs candidate then
          recurse (#2 (Term.dest_abs candidate)) [] entries
        else if Term.is_const candidate orelse
                is_generated_const candidate then
          if skippable candidate then entries
          else update candidate (length arguments) entries
        else entries
    in
      recurse term [] table
    end

  fun uncurry_term table term =
    let
      fun lookup candidate = Option.map #2
        (List.find (Term.aconv candidate o #1) table)
      fun recurse candidate arguments =
        if Term.is_comb candidate then
          let val (function, argument) = Term.dest_comb candidate
          in recurse function (recurse argument [] :: arguments) end
        else if Term.is_abs candidate then
          let val (variable, body) = Term.dest_abs candidate
          in MFH.s_betapplys
            (Term.mk_abs (variable, recurse body []), arguments) end
        else if Term.is_const candidate orelse
                is_generated_const candidate then
          (case lookup candidate of
               SOME arity =>
                 if arity < 2 then MFH.s_betapplys (candidate, arguments)
                 else
                   let
                     val (all_argument_tys, result_ty) =
                       boolSyntax.strip_fun (Term.type_of candidate)
                     val argument_tys = List.take (all_argument_tys, arity)
                     val prefix =
                       if MFH.is_iterator_type (hd argument_tys) then 1
                       else
                         let
                           fun count [] result = result
                             | count (ty :: tys) result =
                                 if ty = Type.bool then count tys (result + 1)
                                 else result
                         in count argument_tys 0 end
                     val tuple_count = arity - prefix
                   in
                     if tuple_count < 2 then
                       MFH.s_betapplys (candidate, arguments)
                     else
                       let
                         val before_arguments = List.take (arguments, prefix)
                         val tuple_arguments = List.take
                           (List.drop (arguments, prefix), tuple_count)
                         val after_arguments = List.drop (arguments, arity)
                         val before_tys = List.take (argument_tys, prefix)
                         val tuple_tys = List.drop (argument_tys, prefix)
                         val remaining_argument_tys =
                           List.drop (all_argument_tys, arity)
                         val tuple_ty = pairSyntax.list_mk_prod tuple_tys
                         val new_ty = boolSyntax.list_mk_fun
                           (before_tys @ [tuple_ty] @ remaining_argument_tys,
                            result_ty)
                         val name = uncurry_prefix_for tuple_count prefix ^
                           uncurry_name candidate
                         val uncurried = MFN.mk_reserved_var name new_ty
                       in
                         MFH.s_betapplys
                           (uncurried,
                            before_arguments @
                            [pairSyntax.list_mk_pair tuple_arguments] @
                            after_arguments)
                       end
                   end
             | NONE => MFH.s_betapplys (candidate, arguments))
        else MFH.s_betapplys (candidate, arguments)
    in
      recurse term []
    end

  fun box_fun_and_pair_in_term context def original =
    let
      fun positive_existential polarity existential =
        (polarity = Util.Pos andalso existential) orelse
        (polarity = Util.Neg andalso not existential)
      fun type_size ty =
        if Type.is_vartype ty then 1
        else 1 + List.foldl (op +) 0
          (map type_size (#Args (Type.dest_thy_type ty)))
      fun env_lookup environment variable =
        Option.map #2 (List.find (Term.aconv variable o #1) environment)
      fun rebind environment variable new_ty body =
        let
          val (name, _) = Term.dest_var variable
          (* A changed binder type may coincide with a free representation
             variable.  Also avoid replacements of outer binders whose
             formerly distinct types collapse under boxing. *)
          val variable' = Term.variant
            (Term.all_vars original @ map #2 environment)
            (Term.mk_var (name, new_ty))
        in (variable', body, (variable, variable') :: environment) end
      fun quantifier environment polarity existential candidate =
        let
          val (variable, body) =
            if existential then boolSyntax.dest_exists candidate
            else boolSyntax.dest_forall candidate
          val old_ty = Term.type_of variable
          val new_ty =
            if polarity = Util.Neut orelse
               positive_existential polarity existential then
              MFH.box_type context MFH.InFunLHS old_ty
            else old_ty
          val (variable', body', environment') =
            rebind environment variable new_ty body
          val transformed = recurse environment' polarity body'
        in
          if existential then boolSyntax.mk_exists (variable', transformed)
          else boolSyntax.mk_forall (variable', transformed)
        end
      and equality environment left right =
        let
          val left' = recurse environment Util.Neut left
          val right' = recurse environment Util.Neut right
          val left_ty = Term.type_of left'
          val right_ty = Term.type_of right'
          val common =
            if def orelse type_size left_ty <= type_size right_ty then left_ty
            else right_ty
        in
          boolSyntax.mk_eq
            (MFH.coerce_term context common left_ty left',
             MFH.coerce_term context common right_ty right')
        end
      and application environment function argument =
        let
          val function' = recurse environment Util.Neut function
          val function_ty = Term.type_of function'
          val (callable, domain_ty) =
            if MFH.is_fun_type function_ty then
              (function', #1 (Type.dom_rng function_ty))
            else if MFH.is_funbox_type function_ty then
              let
                val arguments = MFH.boxed_type_args function_ty
                val domain = List.nth (arguments, 0)
                val range = List.nth (arguments, 1)
                val constructor = hd
                  (MFH.data_type_constrs context function_ty)
                val underlying_ty = Type.-->(domain, range)
              in
                (MFH.select_nth_constr_arg context constructor function' 0
                   underlying_ty, domain)
              end
            else raise err "box_fun_and_pair_in_term"
              "application operator has a nonfunction type"
          val argument' = recurse environment Util.Neut argument
          val old_argument_ty = Term.type_of argument'
        in
          MFH.s_betapply
            (callable, MFH.coerce_term context domain_ty old_argument_ty
              argument')
        end
      and constant candidate =
        let
          val ty = Term.type_of candidate
          val new_ty =
            if (case Lib.total Term.dest_var candidate of
                    SOME (name, _) => MFN.is_quot_normal_name name
                  | NONE => false) then
              let
                val (domain, _) = Type.dom_rng ty
                val boxed = MFH.box_type context MFH.InFunLHS domain
              in Type.-->(boxed, boxed) end
            else if MFH.is_descr candidate andalso MFH.is_fun_type ty then
              let
                val result_ty = #2 (Type.dom_rng ty)
                val boxed_result =
                  MFH.box_type context MFH.InFunLHS result_ty
              in
                Type.-->(Type.-->(boxed_result, Type.bool), boxed_result)
              end
            else if MFH.is_built_in_const candidate then ty
            else if MFH.is_nonfree_constr candidate then
              MFH.box_type context MFH.InConstr ty
            else if (case Lib.total Term.dest_var candidate of
                        SOME (name, _) => MFN.is_sel name
                      | NONE => MFH.is_record_get candidate) then
              MFH.box_type context MFH.InSel ty
            else MFH.box_type context MFH.InExpr ty
        in
          MFH.retype_constant "box" candidate new_ty
        end
      and recurse environment polarity candidate =
        if boolSyntax.is_forall candidate then
          quantifier environment polarity false candidate
        else if boolSyntax.is_exists candidate then
          quantifier environment polarity true candidate
        else if boolSyntax.is_eq candidate then
          let val (left, right) = boolSyntax.dest_eq candidate
          in equality environment left right end
        else if boolSyntax.is_neg candidate then
          boolSyntax.mk_neg (recurse environment
            (Util.flip_polarity polarity) (boolSyntax.dest_neg candidate))
        else if boolSyntax.is_imp_only candidate then
          let val (left, right) = boolSyntax.dest_imp candidate
          in boolSyntax.mk_imp
            (recurse environment (Util.flip_polarity polarity) left,
             recurse environment polarity right)
          end
        else if boolSyntax.is_conj candidate then
          let val (left, right) = boolSyntax.dest_conj candidate
          in boolSyntax.mk_conj
            (recurse environment polarity left,
             recurse environment polarity right)
          end
        else if boolSyntax.is_disj candidate then
          let val (left, right) = boolSyntax.dest_disj candidate
          in boolSyntax.mk_disj
            (recurse environment polarity left,
             recurse environment polarity right)
          end
        else if Term.is_comb candidate then
          let val (function, argument) = Term.dest_comb candidate
          in application environment function argument end
        else if Term.is_abs candidate then
          let
            val (variable, body) = Term.dest_abs candidate
            val (variable', body', environment') =
              rebind environment variable (Term.type_of variable) body
          in
            Term.mk_abs (variable', recurse environment' Util.Neut body')
          end
        else if Term.is_var candidate then
          (case env_lookup environment candidate of
               SOME replacement => replacement
             | NONE =>
                 if is_generated_const candidate then
                   constant candidate
                 else
                   (* Upstream boxes a Free unconditionally and consults its
                      definition's left-hand side only for a schematic Var
                      (nitpick_preproc.ML, [do_term]).  HOL4 has no kernel
                      Var: upstream's Frees and its schematic Vars -- the
                      congruence and bound stand-in variables of
                      [is_schematic_var], which reach here inside congruence
                      and specialized axioms -- are both plain variables, so
                      this branch stands in for upstream's Free and Var
                      cases.  Making [def] unbox one silently splits it from
                      its boxed twin in the negated goal, which
                      specialization puts in the same problem, and leaves the
                      definition constraining nothing. *)
                   let val (name, ty) = Term.dest_var candidate
                   in
                     Term.mk_var (name, MFH.box_type context MFH.InExpr ty)
                   end)
        else if Term.is_const candidate then constant candidate
        else candidate
    in
      recurse [] Util.Pos original
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
        (context as
          {binary_ints, boxes, destroy_constrs, needs, ...} : context)
        assumptions negated =
    let
      val prepared = negated
        |> MFH.unfold_defs_in_term context
        |> close_form
        |> skolemize_term_and_more context max_skolem_depth
        |> specialize_consts_in_term context false 0
      val (nondefinitions, definitions, got_all_mono_user_axioms,
           no_poly_user_axioms) =
        axioms_for_term context assumptions prepared
      (* A concrete-width word is its own numeric carrier: the encoder reads
         a word atom's value from its universe index, which is its Kodkod
         integer only while [int_bounds] stays sequential - that is, while
         binarization is off.  The numeral inside a word literal ([5w] is
         [n2w 5]) would otherwise switch binarization on and leave every
         word atom without an integer value, so a word type vetoes the smart
         choice.  [:char] is the same carrier and vetoes for the same reason,
         its literals being [CHR] of a numeral.  A typedef over [num] or
         [int] vetoes it for a second reason: binarized, its bound is a
         numeral needing a carrier atom of its own, which no scope the search
         grows in lockstep provides.  A forced [binary_ints] still wins in
         every case; the encoder then refuses the word or char operation by
         name, and reaches the typedef only at a hand-named [card num]. *)
      val all_axioms = nondefinitions @ definitions
      val vetoes_binarization = MFH.binarization_veto_test ()
      val binarize =
        case binary_ints of
            SOME false => false
          | _ =>
              List.all (may_use_binary_ints false) nondefinitions andalso
              List.all (may_use_binary_ints true) definitions andalso
              (binary_ints = SOME true orelse
               (List.exists should_use_binary_ints all_axioms andalso
                not (List.exists vetoes_binarization all_axioms)))
      val box = List.exists (fn (_, value) => value <> SOME false) boxes
      val uncurry_terms =
        if binarize then map binarize_nat_and_int_in_term all_axioms
        else all_axioms
      val uncurry_table =
        if box then
          List.foldl (fn (term, table) =>
            add_to_uncurry_table context term table) [] uncurry_terms
        else []
      fun do_middle definitional term =
        let
          val binarized =
            if binarize then binarize_nat_and_int_in_term term else term
        in
          if box then
            binarized
            |> uncurry_term uncurry_table
            |> box_fun_and_pair_in_term context definitional
          else binarized
        end
      val need_ts =
        case needs of
            SOME terms => map (fn term =>
              do_middle false (MFH.unfold_defs_in_term context term)) terms
          (* Upstream leaves automatic needed-value inference as a FIXME.
             NONE therefore deliberately enables no needed-value reasoning. *)
          | NONE => []
      val nondefinitions' = map (fn term =>
        do_tail context false destroy_constrs (do_middle false term))
        nondefinitions
      val definitions' = map (fn term =>
        do_tail context true destroy_constrs (do_middle true term))
        definitions
    in
      (nondefinitions', definitions', need_ts, got_all_mono_user_axioms,
       no_poly_user_axioms, binarize)
    end
end
