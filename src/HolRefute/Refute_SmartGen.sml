(* Horn-shaped Boolean function recognition for smart generators.
   This module deliberately implements only the Horn slice: it reads existing
   defining equations, checks their constructor-pattern coverage, and converts
   them syntactically to intro triples.  It neither flattens functions nor
   creates theory definitions. *)
structure Refute_SmartGen = struct
  type intro_triple =
    {variables : term list, side : term list,
     main : term list, conclusion : term}

  datatype pattern = Wild | Constructor of term * pattern list

  fun same_term left right = Term.aconv left right

  fun member_term term = List.exists (same_term term)

  fun distinct_terms [] = true
    | distinct_terms (term :: rest) =
        not (member_term term rest) andalso distinct_terms rest

  fun same_term_set left right =
    List.all (fn term => member_term term right) left andalso
    List.all (fn term => member_term term left) right

  fun same_constant_symbol left right =
    Term.is_const left andalso Term.is_const right andalso
    Term.same_const left right
    handle HOL_ERR _ => false

  fun same_constant left right =
    same_constant_symbol left right andalso
    Term.type_of left = Term.type_of right
    handle HOL_ERR _ => false

  fun constructors_for ty =
    let
      (* The nchotomy theorem is the authoritative exhaustiveness witness.
         In particular, a collection of terms merely marked as constructors
         is not enough to establish that a pattern matrix covers its type. *)
      val cases = TypeBase.nchotomy_of ty
      val _ = if Theory.uptodate_thm cases then ()
        else raise Feedback.mk_HOL_ERR "Refute_SmartGen"
          "constructors_for" "stale TypeBase cases theorem"
      val constructors =
        map (TypeBasePure.cinst ty) (TypeBase.constructors_of ty)
      val _ = if null constructors then
          raise Feedback.mk_HOL_ERR "Refute_SmartGen"
            "constructors_for" "empty constructor family"
        else ()
    in
      constructors
    end

  fun parse_pattern term =
    if Term.is_var term then SOME (Wild, [term])
    else
      let
        val (head, arguments) = HolKernel.strip_comb term
        val (domains, range) = boolSyntax.strip_fun (Term.type_of head)
        val family = constructors_for (Term.type_of term)
        val constructor = Term.is_const head andalso
          TypeBase.is_constructor head andalso
          length arguments = length domains andalso
          range = Term.type_of term andalso
          List.exists (same_constant head) family
        val children = List.mapPartial parse_pattern arguments
      in
        if constructor andalso length children = length arguments then
          SOME (Constructor (head, map #1 children),
                List.concat (map #2 children))
        else NONE
      end
      handle HOL_ERR _ => NONE

  fun constructor_arity constructor =
    length (#1 (boolSyntax.strip_fun (Term.type_of constructor)))

  fun specialize constructor row =
    case row of
        [] => NONE
      | Wild :: rest =>
          SOME (List.tabulate (constructor_arity constructor, fn _ => Wild) @
                rest)
      | Constructor (other, arguments) :: rest =>
          if same_constant constructor other then SOME (arguments @ rest)
          else NONE

  fun exhaustive rows =
    if null rows then false
    else if List.exists null rows then true
    else if List.all (fn row => case hd row of Wild => true | _ => false)
      rows then
        exhaustive (map tl rows)
    else
      let
        val sample = valOf (Lib.get_first (fn row =>
          case hd row of
              Constructor (constructor, _) => SOME constructor
            | Wild => NONE) rows)
        val (_, result_ty) = boolSyntax.strip_fun (Term.type_of sample)
        val constructors = constructors_for result_ty
        fun covers constructor =
          exhaustive (List.mapPartial (specialize constructor) rows)
      in
        List.all covers constructors
      end
      handle HOL_ERR _ => false
           | Option.Option => false

  fun forbidden_formula term =
    boolSyntax.is_conj term orelse boolSyntax.is_disj term orelse
    boolSyntax.is_imp term orelse boolSyntax.is_neg term orelse
    boolSyntax.is_forall term orelse boolSyntax.is_exists term orelse
    boolSyntax.is_exists1 term orelse boolSyntax.is_cond term orelse
    boolSyntax.is_bool_case term orelse
    boolSyntax.is_literal_case term orelse boolSyntax.is_let term orelse
    boolSyntax.is_select term orelse boolSyntax.is_res_forall term orelse
    boolSyntax.is_res_exists term orelse
    boolSyntax.is_res_exists_unique term orelse
    boolSyntax.is_res_select term orelse
    boolSyntax.is_res_abstract term

  val forbidden_value_heads =
    [boolSyntax.equality, boolSyntax.implication, boolSyntax.select,
     boolSyntax.universal, boolSyntax.existential, boolSyntax.exists1,
     boolSyntax.conjunction, boolSyntax.disjunction, boolSyntax.negation,
     boolSyntax.conditional, boolSyntax.bool_case,
     boolSyntax.literal_case, boolSyntax.let_tm,
     boolSyntax.res_forall_tm, boolSyntax.res_exists_tm,
     boolSyntax.res_exists1_tm, boolSyntax.res_select_tm,
     boolSyntax.res_abstract_tm]

  fun forbidden_value_head term =
    Term.is_const term andalso
    List.exists (fn logical => Term.same_const term logical)
      forbidden_value_heads
    handle HOL_ERR _ => false

  (* Higher-order values are legitimate atom arguments: SORTED's relation
     parameter is the canonical example.  What matters at this layer is
     syntactic opacity, not mode support (TASK_09 degrades unsupported modes).
     Traverse the whole value so that no lambda or logical syntax can be
     smuggled inside an otherwise acceptable application.  Equality itself is
     admitted only by positive_atom, never as a nested value. *)
  fun atom_value term =
    not (Term.is_abs term) andalso not (forbidden_formula term) andalso
    not (forbidden_value_head term) andalso
    if Term.is_var term orelse Term.is_const term then true
    else if Term.is_comb term then
      let val (operator, operand) = HolKernel.dest_comb term
      in atom_value operator andalso atom_value operand end
    else false
    handle HOL_ERR _ => false

  fun predicate_application term =
    not (forbidden_formula term) andalso not (boolSyntax.is_eq term) andalso
    Term.type_of term = Type.bool andalso
    let
      val (head, arguments) = HolKernel.strip_comb term
    in
      not (null arguments) andalso
      (Term.is_const head orelse Term.is_var head)
    end
    handle HOL_ERR _ => false

  fun positive_atom term =
    same_term term boolSyntax.T orelse same_term term boolSyntax.F orelse
    (if boolSyntax.is_eq term then
       let val (left, right) = boolSyntax.dest_eq term
       in atom_value left andalso atom_value right
       end
     else
       predicate_application term andalso atom_value term)

  (* Stored equations such as ALL_DISTINCT_CONS use [~MEM h t].  Negation is
     not an atom in the accepted positive Horn slice, so normalize only this
     syntactic negative-predicate idiom to the equivalent Boolean equality
     [MEM h t = F] before validation.  A negative recursive call consequently
     contains the defined constant below an equality and is rejected by the
     direct-recursive-head check. *)
  fun normalize_negative_predicate term =
    if boolSyntax.is_neg term then
      let val predicate = boolSyntax.dest_neg term
      in
        if predicate_application predicate then
          boolSyntax.mk_eq (predicate, boolSyntax.F)
        else term
      end
    else term

  fun rhs_atoms rhs =
    let
      val atoms = map normalize_negative_predicate
        (boolSyntax.strip_conj rhs)
    in
      if List.all positive_atom atoms then
        SOME (List.filter (fn term => not (same_term term boolSyntax.T)) atoms)
      else NONE
    end

  fun mentions constant term =
    List.exists (same_constant constant)
      (HolKernel.find_terms Term.is_const term)

  (* If the defined constant occurs in an atom, its sole occurrence must be
     that atom's outer head.  In particular, an outer recursive call does not
     excuse another call hidden in one of its arguments. *)
  fun valid_recursive_atom constant atom =
    let
      val occurrences = length
        (List.filter (same_constant_symbol constant)
          (HolKernel.find_terms Term.is_const atom))
      val outer_head = #1 (HolKernel.strip_comb atom)
    in
      occurrences = 0 orelse
      (occurrences = 1 andalso same_constant constant outer_head)
    end
    handle HOL_ERR _ => false

  fun close_free term =
    boolSyntax.list_mk_forall (Term.free_vars_lr term, term)

  type clause =
    {variables : term list, patterns : pattern list,
     premises : term list, conclusion : term}

  fun recognize_clause constant arity raw =
    let
      val (variables, body) = boolSyntax.strip_forall (close_free raw)
      val (left, right) = boolSyntax.dest_eq body
      val (head, arguments) = HolKernel.strip_comb left
      val parsed = List.mapPartial parse_pattern arguments
      val pattern_variables = List.concat (map #2 parsed)
      val premises = valOf (rhs_atoms right)
      (* Repeated pattern variables are retained in [left]/[conclusion].  They
         are intentionally not linearized here: a later compiler can turn the
         repeats into residual equality checks. *)
      val _ = if same_constant head constant andalso
                     length arguments = arity andalso
                     length parsed = arity andalso
                     distinct_terms variables andalso
                     same_term_set variables pattern_variables andalso
                     List.all (valid_recursive_atom constant) premises
              then ()
              else raise Feedback.mk_HOL_ERR "Refute_SmartGen"
                "recognize_clause" "non-Horn equation"
    in
      SOME {variables = variables, patterns = map #1 parsed,
            premises = premises, conclusion = left}
    end
    handle HOL_ERR _ => NONE
         | Option.Option => NONE

  fun triple_of constant
        ({variables, premises, conclusion, ...} : clause) =
    let
      val (main, side) = List.partition (mentions constant) premises
    in
      {variables = variables, side = side, main = main,
       conclusion = conclusion} : intro_triple
    end

  fun recognize_horn_equations constant equations =
    let
      val (domains, range) = boolSyntax.strip_fun (Term.type_of constant)
      val _ = if Term.is_const constant andalso range = Type.bool andalso
                     not (null equations)
              then ()
              else raise Feedback.mk_HOL_ERR "Refute_SmartGen"
                "recognize_horn_equations" "not a Boolean function"
      val clauses = List.mapPartial
        (recognize_clause constant (length domains)) equations
      val _ = if length clauses = length equations andalso
                     exhaustive (map #patterns clauses)
              then ()
              else raise Feedback.mk_HOL_ERR "Refute_SmartGen"
                "recognize_horn_equations" "malformed or incomplete clauses"
    in
      SOME (map (triple_of constant) clauses)
    end
    handle HOL_ERR _ => NONE

  fun theorem_term theorem =
    let
      val proposition =
        boolSyntax.list_mk_imp (Thm.hyp theorem, Thm.concl theorem)
    in
      close_free proposition
    end

  fun equation_source constant =
    (case DefnBase.lookup_userdef constant of
         SOME {const = generic, thm = DefnBase.STDEQNS theorem, ...} =>
           let
             val theta = Type.match_type (Term.type_of generic)
               (Term.type_of constant)
             val theorem = Thm.INST_TYPE theta theorem
             val _ = if Theory.uptodate_thm theorem then ()
               else raise Feedback.mk_HOL_ERR "Refute_SmartGen"
                 "equation_source" "stale defining equations"
             val clauses = map theorem_term (Drule.CONJUNCTS theorem)
           in
             SOME (theorem_term theorem, clauses)
           end
       | _ => NONE)
    handle HOL_ERR _ => NONE

  type cache_entry =
    {constant : term, stamp : term option,
     result : intro_triple list option}

  (* Positive and negative results are session-local ML state.  The source
     stamp prevents a transient current-theory presentation from poisoning a
     later definition with the same name after snapshot/revert. *)
  val intro_cache : cache_entry list ref = ref []

  fun same_stamp NONE NONE = true
    | same_stamp (SOME left) (SOME right) = same_term left right
    | same_stamp _ _ = false

  fun cache_result constant stamp result =
    intro_cache := {constant = constant, stamp = stamp, result = result} ::
      List.filter (fn {constant = other, ...} =>
        not (same_constant constant other)) (!intro_cache)

  fun horn_intro_triples_for constant =
    if not (Term.is_const constant) then NONE
    else
      let
        val source = equation_source constant
        val stamp = Option.map #1 source
        val cached = List.find (fn {constant = other, stamp = old, ...} =>
          same_constant constant other andalso same_stamp stamp old)
          (!intro_cache)
      in
        case cached of
            SOME {result, ...} => result
          | NONE =>
              let
                val result =
                  case source of
                      SOME (_, equations) =>
                        recognize_horn_equations constant equations
                    | NONE => NONE
                val _ = cache_result constant stamp result
              in
                result
              end
      end

  fun clear_intro_cache () = intro_cache := []
  fun intro_cache_size () = length (!intro_cache)
end
