(* Horn sources and positive first-order mode inference for smart generators.
   This module reads existing equations, checks their constructor-pattern
   coverage, converts them syntactically to intro triples, and mode-checks
   Horn SCCs.  It neither flattens functions nor creates theory definitions. *)
structure Refute_SmartGen = struct
  type term = Term.term

  type intro_triple =
    {variables : term list, side : term list,
     main : term list, conclusion : term}

  (* Intro tables deliberately retain their established split [main]/[side]
     shape.  Inference never tries to recover source order from that lossy
     view: every origin constructs one of these records before partitioning. *)
  type inference_clause =
    {side : term list, main : term list, head : term,
     ordered : term list}

  datatype pattern = Wild | Constructor of term * pattern list

  val same_term = Term.aconv

  val member_term = Refute_Util.aconv_member

  fun distinct_terms [] = true
    | distinct_terms (term :: rest) =
        not (member_term term rest) andalso distinct_terms rest

  fun same_term_set left right =
    List.all (fn term => member_term term right) left andalso
    List.all (fn term => member_term term left) right

  fun same_constant_symbol left right =
    Term.is_const left andalso Term.is_const right andalso
    Term.same_const left right
    handle Feedback.HOL_ERR _ => false

  fun same_constant left right =
    same_constant_symbol left right andalso
    Term.type_of left = Term.type_of right
    handle Feedback.HOL_ERR _ => false

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
      handle Feedback.HOL_ERR _ => NONE

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
      handle Feedback.HOL_ERR _ => false
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
    handle Feedback.HOL_ERR _ => false

  (* Higher-order values are legitimate atom arguments: SORTED's relation
     parameter is the canonical example.  What matters at this layer is
     syntactic opacity, not mode support; unsupported modes degrade safely.
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
    handle Feedback.HOL_ERR _ => false

  fun predicate_application term =
    not (forbidden_formula term) andalso not (boolSyntax.is_eq term) andalso
    Term.type_of term = Type.bool andalso
    let
      val (head, arguments) = HolKernel.strip_comb term
    in
      not (null arguments) andalso
      (Term.is_const head orelse Term.is_var head)
    end
    handle Feedback.HOL_ERR _ => false

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
    handle Feedback.HOL_ERR _ => false

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
    handle Feedback.HOL_ERR _ => NONE
         | Option.Option => NONE

  type horn_clause =
    {variables : term list, patterns : pattern list,
     inference : inference_clause}

  fun horn_clause_of constant
        ({variables, patterns, premises, conclusion} : clause) =
    let
      (* Capture [premises] first.  Once partitioned, this interleaving is not
         derivable, even when two clauses have identical split views. *)
      val ordered = premises
      val (main, side) = List.partition (mentions constant) ordered
      val inference =
        {side = side, main = main, head = conclusion,
         ordered = ordered} : inference_clause
    in
      {variables = variables, patterns = patterns,
       inference = inference} : horn_clause
    end

  fun recognize_horn_sources constant equations =
    let
      val (domains, range) = boolSyntax.strip_fun (Term.type_of constant)
      val _ = if Term.is_const constant andalso range = Type.bool andalso
                     not (null equations)
              then ()
              else raise Feedback.mk_HOL_ERR "Refute_SmartGen"
                "recognize_horn_equations" "not a Boolean function"
      val raw = List.mapPartial
        (recognize_clause constant (length domains)) equations
      val _ = if length raw = length equations andalso
                     exhaustive (map #patterns raw)
              then ()
              else raise Feedback.mk_HOL_ERR "Refute_SmartGen"
                "recognize_horn_equations" "malformed or incomplete clauses"
    in
      SOME (map (horn_clause_of constant) raw)
    end
    handle Feedback.HOL_ERR _ => NONE

  fun intro_triple_of
        ({variables, patterns = _,
          inference = {side, main, head, ...}} : horn_clause) =
    {variables = variables, side = side, main = main,
     conclusion = head} : intro_triple

  fun recognize_horn_clauses constant equations =
    Option.map (map #inference)
      (recognize_horn_sources constant equations)

  (* Keep the established public intro-triple result, but do not retain any
     side channel from it into inference. *)
  fun recognize_horn_equations constant equations =
    Option.map (map intro_triple_of)
      (recognize_horn_sources constant equations)

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
    handle Feedback.HOL_ERR _ => NONE

  type cache_entry =
    {constant : term, stamp : term option,
     result : horn_clause list option}

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

  fun cached_horn_sources_for constant =
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
                        recognize_horn_sources constant equations
                    | NONE => NONE
                val _ = cache_result constant stamp result
              in
                result
              end
      end

  fun horn_intro_triples_for constant =
    Option.map (map intro_triple_of) (cached_horn_sources_for constant)

  fun horn_inference_clauses_for constant =
    Option.map (map #inference) (cached_horn_sources_for constant)

  fun clear_intro_cache () = intro_cache := []
  fun intro_cache_size () = length (!intro_cache)

  fun remove_term_once _ [] = NONE
    | remove_term_once term (candidate :: rest) =
        if same_term term candidate then SOME rest
        else Option.map (fn suffix => candidate :: suffix)
          (remove_term_once term rest)

  fun same_term_multiset [] right = null right
    | same_term_multiset (term :: left) right =
        (case remove_term_once term right of
             SOME rest => same_term_multiset left rest
           | NONE => false)

  (* Goal and theorem-table clients have an intro triple and the originating
     ordered premise list at the same time.  Construct the internal record at
     that boundary; never look it up later by the partitioned triple. *)
  fun inference_clause_of_triple ordered
        ({side, main, conclusion, ...} : intro_triple) =
    if same_term_multiset ordered (main @ side) then
      SOME ({side = side, main = main, head = conclusion,
             ordered = ordered} : inference_clause)
    else
      NONE

  (* Modes describe which parts of a predicate call are known on entry.
     [Fun] is used only to curry the modes of a predicate itself.  A [Fun]
     below an argument position is deliberately not inferred: that is the
     higher-order fragment from which this port degrades. *)
  datatype mode =
      Bool
    | Input
    | Output
    | Pair of mode * mode
    | Fun of mode * mode

  datatype mode_derivation =
      Mode_App of mode_derivation * mode_derivation
    | Context of mode
    | Mode_Pair of mode_derivation * mode_derivation
    | Term_Mode of mode

  datatype indprem =
      Prem of term
    | Sidecond of term
    | Generator of term

  type moded_clause =
    {arguments : term list,
     premises : (indprem * mode_derivation) list,
     needs_generator : bool}

  type relation_modes =
    {relation : term,
     modes : (mode * moded_clause list * bool) list}

  datatype external_status =
      Compiled of
        {modes : (mode * bool) list,
         functional : mode list}
    | Uncompiled

  datatype degradation =
      HigherOrderParameters of term
    | CrossGroupReference of term

  type inference_result =
    {relations : relation_modes list,
     degradation : degradation list}

  type premise_score =
    {missing : int,
     functional : bool,
     generator : bool,
     outputs : int,
     recursive : bool}

  fun eq_mode (Fun (left1, left2), Fun (right1, right2)) =
        eq_mode (left1, right1) andalso eq_mode (left2, right2)
    | eq_mode (Pair (left1, left2), Pair (right1, right2)) =
        eq_mode (left1, right1) andalso eq_mode (left2, right2)
    | eq_mode (Pair (left, right), Input) =
        eq_mode (left, Input) andalso eq_mode (right, Input)
    | eq_mode (Pair (left, right), Output) =
        eq_mode (left, Output) andalso eq_mode (right, Output)
    | eq_mode (Input, Pair (left, right)) =
        eq_mode (Input, left) andalso eq_mode (Input, right)
    | eq_mode (Output, Pair (left, right)) =
        eq_mode (Output, left) andalso eq_mode (Output, right)
    | eq_mode (Input, Input) = true
    | eq_mode (Output, Output) = true
    | eq_mode (Bool, Bool) = true
    | eq_mode _ = false

  fun list_mode [] = Bool
    | list_mode (mode :: modes) = Fun (mode, list_mode modes)

  fun strip_mode (Fun (mode, rest)) = mode :: strip_mode rest
    | strip_mode Bool = []
    | strip_mode _ =
        raise Feedback.mk_HOL_ERR "Refute_SmartGen" "strip_mode"
          "predicate mode does not end in Bool"

  fun mode_of (Context mode) = mode
    | mode_of (Term_Mode mode) = mode
    | mode_of (Mode_Pair (left, right)) =
        Pair (mode_of left, mode_of right)
    | mode_of (Mode_App (operator, operand)) =
        (case mode_of operator of
             Fun (domain, range) =>
               if eq_mode (domain, mode_of operand) then range
               else raise Feedback.mk_HOL_ERR "Refute_SmartGen"
                 "mode_of" "mode application does not match"
           | _ => raise Feedback.mk_HOL_ERR "Refute_SmartGen"
               "mode_of" "mode operator is not a function")

  fun head_mode_of derivation =
    let
      fun head (Mode_App (operator, _)) = head operator
        | head other = other
    in
      mode_of (head derivation)
    end

  fun mode_string Bool = "bool"
    | mode_string Input = "i"
    | mode_string Output = "o"
    | mode_string (Pair (left, right)) =
        "(" ^ mode_string left ^ " * " ^ mode_string right ^ ")"
    | mode_string (Fun (domain, range)) =
        mode_string domain ^ " => " ^ mode_string range

  fun contains_function_type ty =
    case Lib.total Type.dom_rng ty of
        SOME _ => true
      | NONE =>
          (case Lib.total Type.dest_type ty of
               SOME (_, arguments) =>
                 List.exists contains_function_type arguments
             | NONE => false)

  val max_mode_space = 256

  fun argument_mode_count ty =
    case Lib.total pairSyntax.dest_prod ty of
        SOME (left, right) =>
          let val left_count = argument_mode_count left
              val right_count = argument_mode_count right
          in
            if left_count > max_mode_space div right_count then
              max_mode_space + 1
            else left_count * right_count
          end
      | NONE => 2

  fun argument_modes ty =
    case Lib.total pairSyntax.dest_prod ty of
        SOME (left, right) =>
          List.concat (map (fn left_mode =>
            map (fn right_mode => Pair (left_mode, right_mode))
              (argument_modes right)) (argument_modes left))
      | NONE => [Input, Output]

  fun all_modes_for relation =
    let
      val (domains, range) = boolSyntax.strip_fun (Term.type_of relation)
    in
      if range = Type.bool andalso
         not (List.exists contains_function_type domains) andalso
         List.foldl (fn (domain, count) =>
           let val modes = argument_mode_count domain
           in
             if count > max_mode_space div modes then max_mode_space + 1
             else count * modes
           end) 1 domains <= max_mode_space then
        let
          (* Never materialize an exponential mode space.  Returning no modes
             safely degrades to the ordinary generator/guard plan. *)
          fun product [] = [[]]
            | product (choices :: rest) =
                List.concat (map (fn choice =>
                  map (fn suffix => choice :: suffix) (product rest))
                    choices)
        in
          map list_mode (product (map argument_modes domains))
        end
      else
        []
    end
    handle Feedback.HOL_ERR _ => []

  fun compare_score
        ({missing = left_missing, functional = left_functional,
          generator = left_generator, outputs = left_outputs,
          recursive = left_recursive} : premise_score,
         {missing = right_missing, functional = right_functional,
          generator = right_generator, outputs = right_outputs,
          recursive = right_recursive} : premise_score) =
    let
      fun lex [] = EQUAL
        | lex (order :: rest) =
            (case order of EQUAL => lex rest | other => other)
      fun preferred flag = if flag then 0 else 1
    in
      lex [Int.compare (left_missing, right_missing),
           Int.compare (preferred left_functional,
                        preferred right_functional),
           Int.compare (preferred (not left_generator),
                        preferred (not right_generator)),
           Int.compare (left_outputs, right_outputs),
           Int.compare (preferred left_recursive,
                        preferred right_recursive)]
    end

  fun output_positions mode =
    let
      fun has_output (Pair (left, right)) =
            has_output left orelse has_output right
        | has_output Output = true
        | has_output _ = false
    in
      length (List.filter has_output (strip_mode mode))
    end

  val union_terms = Refute_Util.union_terms

  fun missing_vars known term =
    List.filter (fn variable => not (member_term variable known))
      (Term.free_vars_lr term)

  fun is_equality_type ty = not (contains_function_type ty)

  fun invertible_head term =
    Term.is_const term andalso TypeBase.is_constructor term
    handle Feedback.HOL_ERR _ => false

  fun noninvertible_subterms term =
    if Term.is_var term then []
    else
      let
        val (head, arguments) = HolKernel.strip_comb term
      in
        if invertible_head head then
          List.concat (map noninvertible_subterms arguments)
        else [term]
      end
    handle Feedback.HOL_ERR _ => [term]

  fun possible_output known term =
    let
      (* HOL4 has no sort discipline that can certify equality on arbitrary
         higher-order values.  In particular, an application [f x] has a
         first-order result type but is still a higher-order output pattern
         when the known free [f] has function type. *)
      fun first_order_known variable =
        not (member_term variable known) orelse
        not (contains_function_type (Term.type_of variable))
    in
      List.all first_order_known (Term.free_vars_lr term) andalso
      List.all (fn subterm =>
        is_equality_type (Term.type_of subterm) andalso
        null (missing_vars known subterm)) (noninvertible_subterms term)
    end

  fun destructable_vars term =
    if Term.is_var term then [term]
    else
      let
        val (head, arguments) = HolKernel.strip_comb term
      in
        if invertible_head head then
          List.concat (map destructable_vars arguments)
        else []
      end
    handle Feedback.HOL_ERR _ => []

  fun derive_argument known term (Pair (left_mode, right_mode)) =
        (case Lib.total pairSyntax.dest_pair term of
             SOME (left, right) =>
               List.concat (map (fn (left_derivation, left_missing) =>
                 map (fn (right_derivation, right_missing) =>
                   (Mode_Pair (left_derivation, right_derivation),
                    union_terms left_missing right_missing))
                   (derive_argument known right right_mode))
                 (derive_argument known left left_mode))
           | NONE => derive_atomic known term
               (Pair (left_mode, right_mode)))
    | derive_argument known term mode = derive_atomic known term mode
  and derive_atomic known term mode =
    if eq_mode (mode, Input) then
      [(Term_Mode Input, missing_vars known term)]
    else if eq_mode (mode, Output) andalso possible_output known term then
      [(Term_Mode Output, [])]
    else
      []

  fun same_relation left right =
    same_constant left right handle Feedback.HOL_ERR _ => false

  fun lookup_assoc relation entries =
    Option.map #2 (List.find (fn (other, _) =>
      same_relation relation other) entries)

  fun premise_head premise =
    let val (head, _) = HolKernel.strip_comb premise
    in if Term.is_const head then SOME head else NONE end
    handle Feedback.HOL_ERR _ => NONE

  fun modes_of table external relation =
    case lookup_assoc relation table of
        SOME modes => SOME (map (fn (mode, _, needs) => (mode, needs)) modes)
      | NONE =>
          (case lookup_assoc relation external of
               SOME (Compiled {modes, ...}) => SOME modes
             | _ => NONE)

  fun functional_mode external relation mode =
    case lookup_assoc relation external of
        SOME (Compiled {functional, ...}) =>
          List.exists (fn candidate => eq_mode (candidate, mode)) functional
      | _ => false

  fun derive_call table external known term =
    let
      val (head, arguments) = HolKernel.strip_comb term
      val infos = Option.getOpt (modes_of table external head, [])
      fun derive (predicate_mode, needs_generator) =
        let
          val argument_mode = strip_mode predicate_mode
          fun step [] [] states = states
            | step (argument :: arguments) (mode :: modes) states =
                step arguments modes
                  (List.concat (map (fn (derivation, missing) =>
                    map (fn (argument_derivation, argument_missing) =>
                      (Mode_App (derivation, argument_derivation),
                       union_terms missing argument_missing))
                      (derive_argument known argument mode)) states))
            | step _ _ _ = []
          val derivations = step arguments argument_mode
            [(Context predicate_mode, [])]
        in
          map (fn (derivation, missing) =>
            (derivation, missing, predicate_mode, needs_generator))
            derivations
        end
    in
      List.concat (map derive infos)
    end
    handle Feedback.HOL_ERR _ => []

  fun classify members external term =
    if boolSyntax.is_neg term then Sidecond term
    else
      case premise_head term of
          NONE => Sidecond term
        | SOME head =>
            if List.exists (same_relation head) members then Prem term
            else
              (case lookup_assoc head external of
                   SOME (Compiled _) => Prem term
                 | _ => Sidecond term)

  fun is_recursive relation term =
    case premise_head term of
        SOME head => same_relation relation head
      | NONE => false

  fun term_of_premise (Prem term) = term
    | term_of_premise (Sidecond term) = term
    | term_of_premise (Generator term) = term

  fun best_derivation relation table external known premise =
    let
      val term = term_of_premise premise
      fun score derivation missing predicate_mode needs_generator =
        {missing = length missing,
         functional = functional_mode external
           (Option.getOpt (premise_head term, term)) predicate_mode,
         generator = needs_generator,
         outputs = output_positions predicate_mode,
         recursive = is_recursive relation term} : premise_score
      val candidates =
        case premise of
            Prem term => map (fn (derivation, missing, mode, random) =>
              (derivation, missing,
               score derivation missing mode random))
              (derive_call table external known term)
          | Sidecond term =>
              [(Context Bool, missing_vars known term,
                {missing = length (missing_vars known term),
                 functional = false, generator = false, outputs = 0,
                 recursive = false})]
          | Generator _ => []
      fun least candidate NONE = SOME candidate
        | least (candidate as (_, _, score))
            (current as SOME (_, _, current_score)) =
            if compare_score (score, current_score) = LESS then
              SOME candidate
            else current
    in
      List.foldl (fn (candidate, current) =>
        least candidate current) NONE candidates
    end

  fun remove_index selected entries =
    List.filter (fn (index, _) => index <> selected) entries

  fun select_premise reorder relation table external known entries =
    let
      val candidates = if reorder then entries else [hd entries]
      fun decorate (index, premise) =
        Option.map (fn (derivation, missing, score) =>
          (index, premise, derivation, missing, score))
          (best_derivation relation table external known premise)
      fun least NONE current = current
        | least candidate NONE = candidate
        | least (candidate as SOME (_, _, _, _, score))
            (current as SOME (_, _, _, _, current_score)) =
            if compare_score (score, current_score) = LESS then
              candidate
            else current
    in
      List.foldl (fn (entry, result) => least (decorate entry) result)
        NONE candidates
    end

  fun split_arguments mode arguments =
    let
      fun combine NONE NONE = NONE
        | combine (SOME term) NONE = SOME term
        | combine NONE (SOME term) = SOME term
        | combine (SOME left) (SOME right) =
            SOME (pairSyntax.mk_pair (left, right))
      fun split_argument (Pair (left_mode, right_mode)) term =
            (case Lib.total pairSyntax.dest_pair term of
                 SOME (left, right) =>
                   let
                     val (left_input, left_output) =
                       split_argument left_mode left
                     val (right_input, right_output) =
                       split_argument right_mode right
                   in
                     (combine left_input right_input,
                      combine left_output right_output)
                   end
               | NONE => split_atomic
                   (Pair (left_mode, right_mode)) term)
        | split_argument argument_mode term =
            split_atomic argument_mode term
      and split_atomic argument_mode term =
        if eq_mode (argument_mode, Input) then (SOME term, NONE)
        else if eq_mode (argument_mode, Output) then (NONE, SOME term)
        else raise Feedback.mk_HOL_ERR "Refute_SmartGen"
          "split_arguments" "argument mode does not match term"
      fun split [] [] inputs outputs = (rev inputs, rev outputs)
        | split (argument_mode :: modes) (term :: terms) inputs outputs =
            let
              val (input, output) = split_argument argument_mode term
              val inputs = case input of SOME value => value :: inputs
                                       | NONE => inputs
              val outputs = case output of SOME value => value :: outputs
                                         | NONE => outputs
            in
              split modes terms inputs outputs
            end
        | split _ _ _ _ =
            raise Feedback.mk_HOL_ERR "Refute_SmartGen"
              "split_arguments" "mode arity mismatch"
    in
      split (strip_mode mode) arguments [] []
    end

  fun check_clause reorder members external table relation mode
        ({side, main, head = conclusion,
          ordered = raw_premises} : inference_clause) =
    let
      val (head, arguments) = HolKernel.strip_comb conclusion
      val _ = if same_relation head relation then ()
        else raise Feedback.mk_HOL_ERR "Refute_SmartGen"
          "check_clause" "clause belongs to another relation"
      val _ = if same_term_multiset raw_premises (main @ side) then ()
        else raise Feedback.mk_HOL_ERR "Refute_SmartGen"
          "check_clause" "ordered premises do not match clause partition"
      val (inputs, outputs) = split_arguments mode arguments
      val initial = union_terms []
        (List.concat (map destructable_vars inputs))
      val premises = map (classify members external) raw_premises
      val indexed = ListPair.zip
        (List.tabulate (length premises, fn index => index), premises)
      fun process known result generated [] =
            SOME (known, result, generated)
        | process known result generated remaining =
            (case select_premise reorder relation table external known
                    remaining of
                 NONE => NONE
               | SOME (index, premise, derivation, missing, _) =>
                   let
                     val generators = rev (map (fn variable =>
                       (Generator variable, Term_Mode Output)) missing)
                     val known' = union_terms known missing
                     val known'' = union_terms known'
                       (Term.free_vars_lr (term_of_premise premise))
                   in
                     process known''
                       (result @ generators @ [(premise, derivation)])
                       (generated orelse not (null missing))
                       (remove_index index remaining)
                   end)
    in
      case process initial [] false indexed of
          NONE => NONE
        | SOME (known, premises, generated) =>
            let
              val head_variables = union_terms []
                (List.concat (map Term.free_vars_lr (inputs @ outputs)))
              val missing = List.filter (fn variable =>
                not (member_term variable known)) head_variables
              val trailing = rev (map (fn variable =>
                (Generator variable, Term_Mode Output)) missing)
            in
              SOME {arguments = arguments,
                    premises = premises @ trailing,
                    needs_generator = generated orelse
                      not (null missing)}
            end
    end
    handle Feedback.HOL_ERR _ => NONE

  fun clauses_for relation clauses =
    List.filter (fn ({head = conclusion, ...} : inference_clause) =>
      case premise_head conclusion of
          SOME head => same_relation relation head
        | NONE => false) clauses

  fun check_relation reorder members external clauses table relation
        modes =
    let
      val clauses = clauses_for relation clauses
      fun check_clauses _ [] checked = SOME (rev checked)
        | check_clauses mode (clause :: rest) checked =
            (case check_clause reorder members external table relation mode
                    clause of
                 NONE => NONE
               | SOME result =>
                   check_clauses mode rest (result :: checked))
      fun check (mode, _, _) =
        if null clauses then NONE
        else
          Option.map (fn checked =>
            (mode, checked, List.exists #needs_generator checked))
            (check_clauses mode clauses [])
    in
      List.mapPartial check modes
    end

  fun same_mode_infos left right =
    length left = length right andalso
    ListPair.allEq (fn ((left_mode, _, left_random),
                        (right_mode, _, right_random)) =>
      eq_mode (left_mode, right_mode) andalso
      left_random = right_random) (left, right)

  fun same_mode_table left right =
    length left = length right andalso
    ListPair.allEq (fn ((left_relation, left_modes),
                        (right_relation, right_modes)) =>
      same_relation left_relation right_relation andalso
      same_mode_infos left_modes right_modes) (left, right)

  fun infer_clauses
        {members, clauses, external, reorder_premises} : inference_result =
    let
      val higher_order = List.filter (null o all_modes_for) members
      fun cross_reference term =
        case premise_head term of
            SOME head =>
              (case lookup_assoc head external of
                   SOME Uncompiled => SOME head
                 | _ => NONE)
          | NONE => NONE
      val cross = List.mapPartial cross_reference
        (List.concat (map (fn ({ordered, ...} : inference_clause) =>
          ordered) clauses))
      fun distinct_relations relations =
        List.foldl (fn (relation, result) =>
          if List.exists (same_relation relation) result then result
          else result @ [relation]) [] relations
      val degradation =
        map HigherOrderParameters higher_order @
        map CrossGroupReference (distinct_relations cross)
      val start = map (fn relation =>
        (relation, map (fn mode => (mode, [], false))
          (all_modes_for relation))) members
      fun iteration table = map (fn (relation, modes) =>
        (relation, check_relation reorder_premises members external
          clauses table relation modes)) table
      fun fixpoint table =
        let val next = iteration table
        in if same_mode_table table next then next else fixpoint next end
      val stable =
        if null higher_order then fixpoint start
        else map (fn relation => (relation, [])) members
      fun materialize (relation, modes) : relation_modes =
        {relation = relation, modes = modes}
    in
      {relations = map materialize stable, degradation = degradation}
    end

  fun infer_group
        {members, clauses, external, reorder_premises} : inference_result =
    infer_clauses
      {members = members, clauses = clauses, external = external,
       reorder_premises = reorder_premises}

  fun source_premises rule =
    let
      val (_, body) = boolSyntax.strip_forall rule
      val (raw_premises, _) = boolSyntax.strip_imp body
    in
      List.concat (map boolSyntax.strip_conj raw_premises)
    end

  fun clause_for_rule triple_for members rule =
    case triple_for members rule of
        SOME triple =>
          inference_clause_of_triple (source_premises rule) triple
      | NONE => NONE

  (* [triple_for] is normally
     [Refute_ModelFinder_HOL.joint_intro_triple_for].  Keeping it as an
     argument preserves SmartGen's independence from the model finder while
     ensuring that one shared SCC and its cross-member calls are inferred in
     a single decreasing fixpoint. *)
  fun infer_scc
        {members, rules, triple_for, external, reorder_premises} =
    let
      val clauses = List.mapPartial
        (clause_for_rule triple_for members) rules
    in
      if length clauses = length rules then
        SOME (infer_clauses
          {members = members, clauses = clauses, external = external,
           reorder_premises = reorder_premises})
      else NONE
    end

  (* The substrate-neutral enumerator is a positive, depth-bounded CPS
     program.  [CpsClause] is [single inputs >>= case-match >>=
     premise-chain >>= single outputs]; the list of clauses is [plus] in
     source order.  Every substrate must preserve these two list orders. *)
  datatype cps_premise =
      CpsCall of {rel : term, mode : mode, ins : term list,
                  outs : term list}
    | CpsGuard of term
    | CpsGenerate of term

  datatype cps_clause = CpsClause of
    {ins : term list, premises : cps_premise list, outs : term list}

  (* The logical fields of an enumerator are not enough to identify the
     definition generation from which they were inferred: snapshot/revert can
     install a same-named constant with an identical printed payload.  Keep a
     session-opaque generation plus a deterministic inference fingerprint and
     bind every compiled plan to that pair. *)
  abstype program_version = ProgramVersion of
    {generation : int, fingerprint : string}
  with
    val source_generation = ref 0

    fun same_program_version
          (ProgramVersion left, ProgramVersion right) = left = right

    fun current_program_version
          (ProgramVersion {generation, ...}) =
      generation = !source_generation

    fun new_program_version fingerprint = ProgramVersion
      {generation = !source_generation, fingerprint = fingerprint}

    fun advance_source_generation () =
      source_generation := !source_generation + 1
  end

  type enumerator =
    {relation : term, mode : mode, version : program_version,
     clauses : cps_clause list}

  fun first_order_mode Input = true
    | first_order_mode Output = true
    | first_order_mode (Pair (left, right)) =
        first_order_mode left andalso first_order_mode right
    | first_order_mode _ = false

  fun compile_premise premise derivation =
    case premise of
        Generator variable => SOME (CpsGenerate variable)
      | Sidecond term => SOME (CpsGuard term)
      | Prem term =>
          let
            val (relation, arguments) = HolKernel.strip_comb term
            val mode = head_mode_of derivation
            val (ins, outs) = split_arguments mode arguments
          in
            if List.all first_order_mode (strip_mode mode) then
              SOME (CpsCall
                {rel = relation, mode = mode, ins = ins, outs = outs})
            else NONE
          end
          handle Feedback.HOL_ERR _ => NONE

  fun compile_clause mode
        ({arguments, premises, ...} : moded_clause) =
    let
      val (ins, outs) = split_arguments mode arguments
      val compiled = map (fn (premise, derivation) =>
        compile_premise premise derivation) premises
    in
      if List.all first_order_mode (strip_mode mode) andalso
         List.all Option.isSome compiled then
        SOME (CpsClause
          {ins = ins, premises = List.mapPartial (fn value => value) compiled,
           outs = outs})
      else NONE
    end
    handle Feedback.HOL_ERR _ => NONE

  fun compile_relation version
        ({relation, modes} : relation_modes) =
    List.mapPartial (fn (mode, clauses, _) =>
      let val compiled = map (compile_clause mode) clauses
      in
        if length compiled = length clauses then
          SOME ({relation = relation, mode = mode, version = version,
                 clauses = List.mapPartial (fn value => value) compiled}
                : enumerator)
        else NONE
      end) modes

  fun inference_fingerprint relations =
    let
      fun clause ({arguments, premises, ...} : moded_clause) =
        String.concatWith ","
          (map Parse.term_to_string
            (arguments @ map (term_of_premise o #1) premises))
      fun relation ({relation, modes} : relation_modes) =
        Parse.term_to_string relation ^ "{" ^
        String.concatWith ";" (map (fn (mode, clauses, needs) =>
          mode_string mode ^ ":" ^ Bool.toString needs ^ ":" ^
          String.concatWith "/" (map clause clauses)) modes) ^ "}"
    in
      String.concatWith "|" (map relation relations)
    end

  type enumerator_cache_entry =
    {relation : term, mode : mode, program : enumerator}

  (* Session-local only: enumerator compilation creates no HOL definition.
     Recompiling a typed relation/mode replaces its previous program. *)
  val enumerator_cache = ref ([] : enumerator_cache_entry list)

  fun same_enumerator_key relation mode
        ({relation = other, mode = other_mode, ...} :
          enumerator_cache_entry) =
    same_relation relation other andalso eq_mode (mode, other_mode)

  fun relation_in relations candidate =
    List.exists (fn ({relation, ...} : relation_modes) =>
      same_relation relation candidate) relations

  (* One assignment replaces the complete inferred group.  This also removes
     modes that disappeared or ceased to compile, rather than leaving an
     obsolete per-mode program behind. *)
  fun cache_inference ({relations, ...} : inference_result) =
    let
      val version = new_program_version (inference_fingerprint relations)
      val programs = List.concat (map (compile_relation version) relations)
      val fresh = map (fn program as {relation, mode, ...} =>
        {relation = relation, mode = mode, program = program}) programs
      val retained = List.filter (fn {relation, ...} =>
        not (relation_in relations relation)) (!enumerator_cache)
    in
      enumerator_cache := fresh @ retained
    end

  fun program_is_fresh ({relation, version, ...} : enumerator) =
    current_program_version version andalso Theory.uptodate_term relation

  fun enumerator_for_in entries relation mode =
    case List.find (same_enumerator_key relation mode) entries of
        SOME {program, ...} =>
          if program_is_fresh program then SOME program else NONE
      | NONE => NONE

  fun enumerator_for relation mode =
    enumerator_for_in (!enumerator_cache) relation mode

  (* A compile invocation takes this immutable value once.  Code extraction
     must resolve the complete recursive closure from that value, never from
     the mutable session cache. *)
  fun enumerator_snapshot () =
    List.filter (program_is_fresh o #program) (!enumerator_cache)

  fun enumerator_gen_types ({clauses, ...} : enumerator) =
    List.concat (map (fn CpsClause {premises, ...} =>
      List.mapPartial (fn CpsGenerate variable =>
        SOME (Term.type_of variable) | _ => NONE) premises) clauses)

  fun invalidate_enumerator_cache _ =
    (advance_source_generation (); enumerator_cache := [])

  val _ = Theory.register_hook
    ("Refute_SmartGen.enumerators", invalidate_enumerator_cache)

  fun clear_enumerator_cache () = invalidate_enumerator_cache ()

  fun relation_modes_for relation
        ({relations, ...} : inference_result) =
    List.find (fn ({relation = other, ...} : relation_modes) =>
      same_relation relation other) relations

  fun top_level_parts mode arguments =
    SOME (split_arguments mode arguments)
    handle Feedback.HOL_ERR _ => NONE

  type goal_mode =
    {mode : mode, ins : term list, outs : term list,
     missing : term list, score : premise_score}

  (* Goal-premise mode selection uses the same five-way order as rule mode
     inference.  Missing input variables are explicit: the plan compiler may
     generate them before the Enum, allowing an earlier equality premise to
     win and bind them instead when premise reordering is enabled. *)
  fun goal_modes_for_call known call inference =
    let
      val (relation, arguments) = HolKernel.strip_comb call
      val relation_result = relation_modes_for relation inference
      fun candidate (mode, _, needs_generator) =
        case top_level_parts mode arguments of
            NONE => NONE
          | SOME (ins, outs) =>
              let
                val missing = List.foldl (fn (input, result) =>
                  union_terms result (missing_vars known input)) [] ins
                val available = union_terms known missing
              in
                if List.all (possible_output available) outs then
                  SOME
                    {mode = mode, ins = ins, outs = outs,
                     missing = missing,
                     score =
                       {missing = length missing, functional = false,
                        generator = needs_generator,
                        outputs = length outs, recursive = false}}
                else NONE
              end
    in
      case relation_result of
          NONE => []
        | SOME {modes, ...} => List.mapPartial candidate modes
    end
    handle Feedback.HOL_ERR _ => []

end
