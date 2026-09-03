(* Horn sources and polarity-split first-order mode inference for smart
   generators.  This module reads existing equations, checks their
   constructor-pattern coverage, converts them syntactically to intro
   triples, and mode-checks Horn SCCs -- both the modes in which a
   relation executes positively, and, conservatively, the modes in
   which its complement does.  [flatten_rhs] also flattens an ordinary
   function's self-recursive defining equations into Horn graph clauses
   (function flattening, in the Isabelle predicate-compiler sense), and
   [infer_graph] mode-checks that graph through the same fixpoint, keyed
   on [Graph f].  The module creates no theory definitions. *)
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
    {patterns : pattern list, premises : term list, conclusion : term}

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
      SOME {patterns = map #1 parsed, premises = premises,
            conclusion = left}
    end
    handle Feedback.HOL_ERR _ => NONE
         | Option.Option => NONE

  fun inference_clause_of constant
        ({premises, conclusion, ...} : clause) =
    let
      (* Capture [premises] first.  Once partitioned, this interleaving is not
         derivable, even when two clauses have identical split views. *)
      val ordered = premises
      val (main, side) = List.partition (mentions constant) ordered
    in
      {side = side, main = main, head = conclusion,
       ordered = ordered} : inference_clause
    end

  fun recognize_horn_sources constant equations =
    let
      val (domains, range) = boolSyntax.strip_fun (Term.type_of constant)
      val _ = if Term.is_const constant andalso range = Type.bool andalso
                     not (null equations)
              then ()
              else raise Feedback.mk_HOL_ERR "Refute_SmartGen"
                "recognize_horn_sources" "not a Boolean function"
      val raw = List.mapPartial
        (recognize_clause constant (length domains)) equations
      val _ = if length raw = length equations andalso
                     exhaustive (map #patterns raw)
              then ()
              else raise Feedback.mk_HOL_ERR "Refute_SmartGen"
                "recognize_horn_sources" "malformed or incomplete clauses"
    in
      SOME (map (inference_clause_of constant) raw)
    end
    handle Feedback.HOL_ERR _ => NONE

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

  type 'a cache_entry =
    {constant : term, stamp : term option, result : 'a list option}

  (* Positive and negative results are session-local ML state.  The source
     stamp prevents a transient current-theory presentation from poisoning a
     later definition with the same name after snapshot/revert. *)
  val intro_cache : inference_clause cache_entry list ref = ref []

  val same_stamp = Lib.option_eq same_term

  fun cached_synthesis (cache : 'a cache_entry list ref) synthesize
        constant =
    if not (Term.is_const constant) then NONE
    else
      let
        val source = equation_source constant
        val stamp = Option.map #1 source
        val cached = List.find (fn {constant = other, stamp = old, ...} =>
          same_constant constant other andalso same_stamp stamp old)
          (!cache)
      in
        case cached of
            SOME {result, ...} => result
          | NONE =>
              let
                val result =
                  case source of
                      SOME (_, equations) => synthesize constant equations
                    | NONE => NONE
                val _ = cache :=
                  {constant = constant, stamp = stamp, result = result} ::
                  List.filter (fn {constant = other, ...} =>
                    not (same_constant constant other)) (!cache)
              in
                result
              end
      end

  fun horn_inference_clauses_for constant =
    cached_synthesis intro_cache recognize_horn_sources constant

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
     higher-order fragment from which this port degrades.
     [Fixed] names one more escape from that fragment: a single closed
     term this argument position is known to hold at every occurrence in
     one inference attempt.  It carries no runtime slot at all -- neither
     [ins] nor [outs] -- because the value is baked into the compiled
     clause bodies by substitution before the clause is ever mode-checked;
     see [infer_fixed_argument].  It is therefore never produced by
     [argument_modes]/[all_modes_for_type], only by
     [fixed_modes_for]. *)
  datatype mode =
      Bool
    | Input
    | Output
    | Pair of mode * mode
    | Fun of mode * mode
    | Fixed of term

  (* A relation key generalises "a Boolean constant" to also denote the
     graph of an ordinary function, without that graph ever existing as
     a term.  [Graph f], for [f : t1 -> ... -> tn -> r], denotes
     [\a1 ... an res. f a1 ... an = res], of arity [n + 1]: maximal and
     fixed by [f]'s type alone (never partial), because a function's
     defining equations are stated at maximal application and a partial
     graph would have no equations to synthesise clauses from.  [Graph]
     values are built at [synthesize_graph_clauses] (transiently, only
     to read [relation_arity]), [infer_graph] (its single member, the
     tag on its clauses, and the relation carried in its result),
     [compile_premise]'s [GraphPrem] branch, and
     [Refute_QC]'s goal-premise recogniser, which is what makes
     [infer_graph]'s result actually reach [cache_inference] -- and
     hence [compile_premise] -- for a goal premise recognising
     [f a1 ... an = res].  [check_clause] builds no [Graph] value
     itself, only [GraphPrem] premises. *)
  datatype relation_key =
      Predicate of term
    | Graph of term

  fun relation_term (Predicate f) = f
    | relation_term (Graph f) = f

  fun relation_type (Predicate f) = Term.type_of f
    | relation_type (Graph f) =
        let val (domains, range) = boolSyntax.strip_fun (Term.type_of f)
        in boolSyntax.list_mk_fun (domains @ [range], Type.bool) end

  (* Type-driven, never equation-driven: [synthesize_graph_clauses] checks
     its equations' own argument count against this, rather than the
     other way around, so a point-free definition (fewer formals than its
     type admits) is caught instead of silently assumed. *)
  fun relation_arity key =
    length (#1 (boolSyntax.strip_fun (relation_type key)))

  (* Equal constructor and equal constant: [Predicate f] and [Graph f]
     are different relations for the same [f] -- different arities and
     different clause sets. *)
  fun same_relation (Predicate left) (Predicate right) =
        same_constant left right
    | same_relation (Graph left) (Graph right) = same_constant left right
    | same_relation _ _ = false

  fun relation_string (Predicate f) = Parse.term_to_string f
    | relation_string (Graph f) = "graph " ^ Parse.term_to_string f

  (* Graph clause synthesis (function inversion, gated by
     [allow_function_inversion]).  One clause per defining equation of a
     function [f]: [arguments] are its LHS patterns, [output] is its RHS
     flattened per [flatten_rhs], and [calls], in left-to-right order, are
     the self-recursive calls that flattening replaced by a fresh
     variable -- each [(call_args, result)] denoting the premise
     [f call_args = result]. *)
  type graph_clause =
    {arguments : term list, output : term,
     calls : (term list * term) list}

  fun fresh_variable used ty = Term.variant used (Term.mk_var ("v", ty))

  (* Flatten one rhs occurrence for [constant]'s own graph, whose defining
     equations apply it to exactly [arity] arguments: a variable or a
     fully-applied constructor over already-flattened subterms stays in
     place; a self-recursive call to [constant] at that same [arity] is
     replaced by a fresh variable, with its own arguments flattened
     first, contributing a premise; anything else -- in particular a call
     to a *different* function, or non-Horn syntax such as a conditional
     -- is refused by returning [NONE], rather than composing with
     another function's graph.  This scopes clause synthesis down to
     self-recursion only; recursively flattening a call to some other
     flattenable function is a strictly more general capability that is
     deliberately not attempted here.  Every shape test below is total
     and structural; the one non-test step, [Term.list_mk_comb]
     rebuilding a constructor application from its flattened arguments,
     is a construction that can raise in principle, but is safe here
     because flattening preserves each subterm's type.  A [NONE] result
     is therefore always a shape refusal, never a swallowed error. *)
  fun flatten_rhs constant arity used term =
    if Term.is_var term then SOME (term, [], used)
    else
      let val (head, arguments) = HolKernel.strip_comb term
      in
        if Term.is_const head andalso TypeBase.is_constructor head andalso
           length (#1 (boolSyntax.strip_fun (Term.type_of head))) =
             length arguments
        then
          Option.map (fn (flattened, calls, used') =>
              (Term.list_mk_comb (head, flattened), calls, used'))
            (flatten_args constant arity used arguments)
        else if same_constant head constant andalso
                length arguments = arity
        then
          case flatten_args constant arity used arguments of
              NONE => NONE
            | SOME (flat_args, calls, used') =>
                let val result = fresh_variable used' (Term.type_of term)
                in
                  SOME (result, calls @ [(flat_args, result)],
                        result :: used')
                end
        else NONE
      end
  and flatten_args _ _ used [] = SOME ([], [], used)
    | flatten_args constant arity used (argument :: rest) =
        case flatten_rhs constant arity used argument of
            NONE => NONE
          | SOME (flat, calls, used') =>
              (case flatten_args constant arity used' rest of
                   NONE => NONE
                 | SOME (flats, more_calls, used'') =>
                     SOME (flat :: flats, calls @ more_calls, used''))

  (* One equation, recognised the same way [recognize_clause] recognises a
     Horn equation: closed, stripped of its leading [!], its LHS parsed as
     [arity] constructor patterns over distinct variables covering the
     whole equation -- reusing [parse_pattern]/[close_free]/
     [distinct_terms]/[same_term_set] rather than duplicating their
     checks -- with the rhs then flattened.  Returns the clause together
     with its LHS patterns, so the caller can run the same [exhaustive]
     check [recognize_horn_sources] runs. *)
  fun recognize_graph_clause constant arity raw =
    let
      val (variables, body) = boolSyntax.strip_forall (close_free raw)
      val (left, right) = boolSyntax.dest_eq body
      val (head, arguments) = HolKernel.strip_comb left
      val parsed = List.mapPartial parse_pattern arguments
      val pattern_variables = List.concat (map #2 parsed)
    in
      if same_constant head constant andalso
         length arguments = arity andalso length parsed = arity andalso
         distinct_terms variables andalso
         same_term_set variables pattern_variables
      then
        case flatten_rhs constant arity (Term.free_vars_lr left) right of
            NONE => NONE
          | SOME (output, calls, _) =>
              SOME (({arguments = arguments, output = output,
                      calls = calls} : graph_clause), map #1 parsed)
      else NONE
    end
    (* No [Option.Option] arm, unlike [recognize_clause]: nothing in this
       body's call graph ([flatten_rhs]/[flatten_args], [parse_pattern],
       [close_free], [distinct_terms], [same_term_set]) calls [valOf] or
       [Option.valOf]; only [Feedback.HOL_ERR] can escape here. *)
    handle Feedback.HOL_ERR _ => NONE

  fun equation_arity raw =
    let
      val (_, body) = boolSyntax.strip_forall (close_free raw)
      val (left, _) = boolSyntax.dest_eq body
    in SOME (length (#2 (HolKernel.strip_comb left))) end
    handle Feedback.HOL_ERR _ => NONE

  (* Synthesise [constant]'s graph clauses from its defining equations, or
     refuse ([NONE]).  Every equation must be recognised ([length raw =
     length equations]) and the surviving patterns must be [exhaustive],
     as for the Horn recogniser -- but that guard is not needed for
     SOUNDNESS here: each equation is a universally-closed conjunct of a
     theorem, so any surviving clause is true at every instance of its
     own patterns, and an exhaustive surviving subset is already a
     complete clause set, since a dropped equation cannot remove a
     derivable fact.  Its job is instead to refuse a definition the code
     does not fully understand, rather than synthesise an
     under-approximating graph from a partial read of it.  The
     arity-agreement check is additional to what [recognize_horn_sources]
     needs, because a function's own type can admit more formals than
     its equations bind:
     [arity], from the equations themselves, must agree with
     [relation_arity (Graph constant)], which [relation_type] computes
     from [constant]'s type alone.  A point-free definition -- fewer
     formals than the type admits -- fails this and is refused rather
     than assumed.  Raises no exception of its own: [equation_arity],
     [recognize_graph_clause] and [exhaustive] each already catch their
     own [Feedback.HOL_ERR], and [relation_arity]/[Term.type_of] cannot
     raise on the well-formed constant [Term.is_const constant] has
     already confirmed by the time [relation_arity (Graph constant)] is
     evaluated. *)
  fun synthesize_graph_clauses constant equations =
    case equations of
        [] => NONE
      | first :: _ =>
          (case equation_arity first of
               NONE => NONE
             | SOME arity =>
                 let
                   val raw = List.mapPartial
                     (recognize_graph_clause constant arity) equations
                 in
                   if Term.is_const constant andalso
                      length raw = length equations andalso
                      exhaustive (map #2 raw) andalso
                      arity + 1 = relation_arity (Graph constant)
                   then SOME (map #1 raw)
                   else NONE
                 end)

  (* Separate from [intro_cache]: a [Graph f] entry and a [Predicate f]
     entry for the same [f] therefore cannot collide, because they are
     never in the same table. *)
  val graph_cache : graph_clause cache_entry list ref = ref []

  (* The sole construction site for clause synthesis outside the accessor
     pins.  The [allow_function_inversion] gate lives in [infer_graph]
     (below), which refuses before calling this, so with the flag off no
     [Graph] key is built. *)
  fun graph_clauses_for constant =
    cached_synthesis graph_cache synthesize_graph_clauses constant

  datatype mode_derivation =
      Mode_App of mode_derivation * mode_derivation
    | Context of mode
    | Mode_Pair of mode_derivation * mode_derivation
    | Term_Mode of mode

  (* [GraphPrem (f, arguments)] is a flattened graph-clause premise:
     [f]'s graph applied to [arguments] ([call_args @ [result]], length
     [relation_arity (Graph f)]).  Distinct from [Prem]: a graph premise
     is never one [strip_comb]-able term ([f]'s own type generally
     cannot accept an extra [result] argument), so it carries its parts
     pre-split rather than a single term to re-derive them from. *)
  datatype indprem =
      Prem of term
    | Sidecond of term
    | Generator of term
    | GraphPrem of term * term list

  type moded_clause =
    {arguments : term list,
     premises : (indprem * mode_derivation) list,
     needs_generator : bool}

  (* What the fixpoint below checks: one clause together with the
     relation it defines.  A Horn clause names that relation in its own
     conclusion, but a graph clause does not -- a graph premise
     [f call_args = result] has arity one more than [f]'s own type, so
     its [strip_comb] head is [$=], not [f].  The key is therefore
     carried rather than re-derived, which is the whole of what graph
     inference needs; both kinds then run through one
     [check_clause]/[check_relation]. *)
  datatype clause_body =
      HornClause of inference_clause
    | GraphClause of graph_clause

  type keyed_clause = {relation : relation_key, body : clause_body}

  type relation_modes =
    {relation : relation_key,
     modes : (mode * moded_clause list * bool) list}

  datatype external_status =
      Compiled of
        {modes : (mode * bool) list,
         functional : mode list}
    | Uncompiled

  (* Which of a relation's modes have a decidable complement.  Only the
     mode is recorded: a complement is compiled from the positive clauses
     in [relations] under the same mode, so those remain the single source
     of truth and this table cannot be mistaken for a positive one.  A
     relation's list is [] whenever decidability cannot be established --
     never an optimistic guess.  Consumed by [Refute_QC]'s premise
     analysis through [complement_available], which builds a closed
     complement condition from the same-mode [enumerator] via
     [Refute_EvalEnum.negation_condition]. *)
  type relation_negative_modes = {relation : relation_key, modes : mode list}

  type inference_result =
    {relations : relation_modes list,
     negative : relation_negative_modes list}

  type premise_score =
    {missing : int,
     functional : bool,
     generator : bool,
     outputs : int,
     recursive : bool}

  fun eq_mode (Fixed left, Fixed right) = same_term left right
    | eq_mode (Fun (left1, left2), Fun (right1, right2)) =
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

  (* [argument_modes] returns [mode] or [] for a function type -- never
     [Input, Output] -- so SmartGen never inverts a predicate value: no
     function-typed position ever carries [Output].
     A mode is "given" iff it contains no [Output] anywhere: an atomic
     [Input] or [Bool], or a [Fun]/[Pair] whose components are all given.
     [Fun] can nest inside [Pair] -- e.g. the mode of [(num -> bool) # num]
     is [Pair (Fun (Input, Bool), Input)] -- so both recurse together
     rather than treating [Fun] as flat or as automatically given. *)
  fun given_mode (Fixed _) = true
    | given_mode Bool = true
    | given_mode (Fun (domain, range)) =
        given_mode domain andalso given_mode range
    | given_mode (Pair (left, right)) =
        given_mode left andalso given_mode right
    | given_mode mode = eq_mode (mode, Input)

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

  fun mode_string (Fixed term) = "=" ^ Parse.term_to_string term
    | mode_string Bool = "bool"
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

  (* A predicate-typed argument -- a curried chain ending in [bool], none
     of whose own argument types contains a function type -- gets the
     single mode that treats it as an opaque decidable test: every one of
     its arguments is [Input].  SmartGen cannot invert it (there is no
     definition to consult, only a bound variable), so no [Output] variant
     is ever offered for it.  A wider function type (non-[bool] range, or
     one that itself takes a predicate) has no safe mode at all: it can be
     neither tested nor inverted, so it gets none. *)
  fun predicate_mode_of ty =
    let val (arguments, range) = boolSyntax.strip_fun ty
    in
      if range = Type.bool andalso not (null arguments) andalso
         not (List.exists contains_function_type arguments)
      then SOME (list_mode (map (fn _ => Input) arguments))
      else NONE
    end

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
      | NONE =>
          if contains_function_type ty then
            (* [argument_modes] already returns [] here, so the product
               is [] regardless; this agrees with it belt-and-braces --
               keep it [max_mode_space + 1], not [0], which would raise
               [Div] at [max_mode_space div right_count] above,
               uncaught by the [Feedback.HOL_ERR] handler. *)
            case predicate_mode_of ty of SOME _ => 1
                                        | NONE => max_mode_space + 1
          else 2

  fun argument_modes ty =
    case Lib.total pairSyntax.dest_prod ty of
        SOME (left, right) =>
          List.concat (map (fn left_mode =>
            map (fn right_mode => Pair (left_mode, right_mode))
              (argument_modes right)) (argument_modes left))
      | NONE =>
          if contains_function_type ty then
            case predicate_mode_of ty of SOME mode => [mode]
                                        | NONE => []
          else [Input, Output]

  (* Cartesian product of a per-position choice list.  Both callers
     ([all_modes_for_type], [fixed_modes_for]) guard it with their own
     [max_mode_space] bound first: an exponential mode space is never
     materialized, and returning no modes safely degrades to the
     ordinary generator/guard plan. *)
  fun product [] = [[]]
    | product (choices :: rest) =
        List.concat (map (fn choice =>
          map (fn suffix => choice :: suffix) (product rest)) choices)

  (* Pure function of a curried Boolean-valued type, so [relation_type]
     drives it uniformly: a [Graph f] key has no term of its own relation
     type, and needs no placeholder one. *)
  fun all_modes_for_type ty =
    let
      val (domains, range) = boolSyntax.strip_fun ty
    in
      if range = Type.bool andalso
         List.foldl (fn (domain, count) =>
           let val modes = argument_mode_count domain
           in
             if count > max_mode_space div modes then max_mode_space + 1
             else count * modes
           end) 1 domains <= max_mode_space then
        map list_mode (product (map argument_modes domains))
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
    (* [Fixed] never derives from an arbitrary term the way [given_mode]
       does: the whole point of the mode is that this position holds one
       particular closed value, so a call whose actual argument there is
       some other term is not an occurrence of the fixed relation and
       must not be mistaken for one. *)
    case mode of
        Fixed expected =>
          if same_term term expected then [(Term_Mode mode, [])] else []
      | _ =>
          if eq_mode (mode, Input) then
            [(Term_Mode Input, missing_vars known term)]
          else if given_mode mode then
            [(Term_Mode mode, missing_vars known term)]
          else if eq_mode (mode, Output) andalso possible_output known term
          then
            [(Term_Mode Output, [])]
          else
            []

  (* [lookup_assoc] reads the external table, which is keyed by bare
     constants: compare with [same_constant].  The fixpoint table is
     keyed by [relation_key] instead -- [Predicate f] and [Graph f] are
     different relations -- so it gets its own [same_relation] lookup. *)
  fun lookup_assoc relation entries =
    Lib.op_assoc1 same_constant relation entries

  fun lookup_modes relation entries =
    Lib.op_assoc1 same_relation relation entries

  fun premise_head premise =
    let val (head, _) = HolKernel.strip_comb premise
    in if Term.is_const head then SOME head else NONE end
    handle Feedback.HOL_ERR _ => NONE

  (* No external entry can ever name a graph: [flatten_rhs] refuses any
     call to another function, so a graph's only callee is itself and its
     modes are always in [table]. *)
  fun modes_of table external relation =
    case lookup_modes relation table of
        SOME modes => SOME (map (fn (mode, _, needs) => (mode, needs)) modes)
      | NONE =>
          (case relation of
               Predicate head =>
                 (case lookup_assoc head external of
                      SOME (Compiled {modes, ...}) => SOME modes
                    | _ => NONE)
             | Graph _ => NONE)

  fun functional_mode external (Predicate head) mode =
        (case lookup_assoc head external of
             SOME (Compiled {functional, ...}) =>
               List.exists (fn candidate => eq_mode (candidate, mode))
                 functional
           | _ => false)
    | functional_mode _ (Graph _) _ = false

  (* One premise's candidate derivations, at every mode its callee
     exports.  [arguments] comes from [strip_comb] for a [Prem] and is
     [call_args @ [result]] for a [GraphPrem]; a callee mode of the wrong
     arity contributes nothing, through [step]'s final clause. *)
  fun derive_call table external known relation arguments =
    let
      val infos = Option.getOpt (modes_of table external relation, [])
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
            if List.exists (fn member =>
                 same_relation member (Predicate head)) members
            then Prem term
            else
              (case lookup_assoc head external of
                   SOME (Compiled _) => Prem term
                 | _ => Sidecond term)

  fun term_of_premise (Prem term) = term
    | term_of_premise (Sidecond term) = term
    | term_of_premise (Generator term) = term
    | term_of_premise (GraphPrem (f, arguments)) =
        boolSyntax.mk_eq
          (Term.list_mk_comb (f, Lib.butlast arguments), List.last arguments)

  (* [relation] is the relation whose clause this premise sits in, so
     [recursive] is key equality against the premise's own callee -- a
     [GraphPrem (f, _)] in [Graph f]'s clauses is always a self-call.
     [Generator] premises are inserted by [check_clause] itself and are
     never offered for selection; the arms are enumerated rather than
     ending in a wildcard so that a new [indprem] constructor fails to
     compile here instead of silently scoring as unusable. *)
  fun best_derivation relation table external known premise =
    let
      fun score callee missing predicate_mode needs_generator =
        {missing = length missing,
         functional = functional_mode external callee predicate_mode,
         generator = needs_generator,
         outputs = output_positions predicate_mode,
         recursive = same_relation relation callee} : premise_score
      fun calls callee arguments =
        map (fn (derivation, missing, mode, random) =>
          (derivation, missing, score callee missing mode random))
          (derive_call table external known callee arguments)
      val candidates =
        case premise of
            Prem term =>
              let val (head, arguments) = HolKernel.strip_comb term
              in calls (Predicate head) arguments end
          | GraphPrem (f, arguments) => calls (Graph f) arguments
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
        (* A [Fixed] position carries no runtime slot: its value is
           already baked into the clause bodies by substitution, so it
           contributes to neither [ins] nor [outs].  Verify the actual
           term still is the fixed value rather than trusting the mode:
           a call site whose argument there differs is not an occurrence
           of this fixed relation and must be rejected, not silently
           treated as a match (this is also what stops one specialised
           enumerator from being attached to a different call site). *)
        case argument_mode of
            Fixed expected =>
              if same_term term expected then (NONE, NONE)
              else raise Feedback.mk_HOL_ERR "Refute_SmartGen"
                "split_arguments" "argument mode does not match term"
          | _ =>
              if given_mode argument_mode then (SOME term, NONE)
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

  (* A clause's head arguments and its premises, in source order.  A Horn
     clause re-derives its relation from its own conclusion and is checked
     against the key it was tagged with; a graph clause's [calls] are
     already split into [(call_args, result)] pairs, each denoting the
     premise [f call_args = result], and its head arguments are the LHS
     patterns followed by the flattened rhs. *)
  fun clause_parts members external relation
        (HornClause ({side, main, head = conclusion,
                      ordered = raw_premises} : inference_clause)) =
        let
          val (head, arguments) = HolKernel.strip_comb conclusion
          val _ = if same_relation relation (Predicate head) then ()
            else raise Feedback.mk_HOL_ERR "Refute_SmartGen"
              "check_clause" "clause belongs to another relation"
          val _ = if same_term_multiset raw_premises (main @ side) then ()
            else raise Feedback.mk_HOL_ERR "Refute_SmartGen"
              "check_clause"
              "ordered premises do not match clause partition"
        in
          (arguments, map (classify members external) raw_premises)
        end
    | clause_parts _ _ (Graph f)
        (GraphClause ({arguments, output, calls} : graph_clause)) =
        (arguments @ [output],
         map (fn (call_args, result) =>
           GraphPrem (f, call_args @ [result])) calls)
    | clause_parts _ _ _ (GraphClause _) =
        raise Feedback.mk_HOL_ERR "Refute_SmartGen"
          "check_clause" "graph clause tagged with a predicate key"

  (* [missing] alone under-reports a graph self-call: an [Output]
     position's [derive_argument] never adds to [missing] (a bare-variable
     output is always [possible_output]), so a call whose own arguments
     are locally resolved can still recurse into a callee mode whose OTHER
     clauses raise a generator at runtime.  Folding in the selected
     candidate's own flag -- already carried by [derive_call] for
     selection -- closes that gap without touching selection itself.  A
     [Prem] has the same gap, but closing it there would move existing
     predicate verdicts, so it stays scoped to graph premises. *)
  fun callee_generator (GraphPrem _) ({generator, ...} : premise_score) =
        generator
    | callee_generator _ _ = false

  fun check_clause reorder members external table relation mode
        ({body, ...} : keyed_clause) =
    let
      val (arguments, premises) =
        clause_parts members external relation body
      val (inputs, outputs) = split_arguments mode arguments
      val initial = union_terms []
        (List.concat (map destructable_vars inputs))
      val indexed = ListPair.zip
        (List.tabulate (length premises, fn index => index), premises)
      fun process known result generated [] =
            SOME (known, result, generated)
        | process known result generated remaining =
            (case select_premise reorder relation table external known
                    remaining of
                 NONE => NONE
               | SOME (index, premise, derivation, missing, score) =>
                   let
                     val generators = rev (map (fn variable =>
                       (Generator variable, Term_Mode Output)) missing)
                     val known' = union_terms known missing
                     val known'' = union_terms known'
                       (Term.free_vars_lr (term_of_premise premise))
                   in
                     process known''
                       (result @ generators @ [(premise, derivation)])
                       (generated orelse not (null missing) orelse
                        callee_generator premise score)
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
    (* Live, not dead: [split_arguments] raises for a [Pair] mode whose
       argument is a bare variable rather than a [dest_pair]-able term
       ([split_atomic] admits only [given_mode] or all-[Output]; a
       [Pair (Input, Output)] mode is neither), and both a Horn head and
       a graph clause's flattened arguments can present exactly that
       shape.  [clause_parts]'s own two assertions land here as well. *)
    handle Feedback.HOL_ERR _ => NONE

  fun clauses_for relation clauses =
    List.filter (fn ({relation = other, ...} : keyed_clause) =>
      same_relation relation other) clauses

  (* Deciding that a clause fails means deciding that one of its premises
     fails, and for a relational call that needs the callee's complement,
     which this inference does not have: a fellow group member's call may be
     cyclic, and an external [Compiled] relation exports positive modes
     only.  Every [Prem] premise therefore blocks; a [Sidecond] does not,
     since the substrate decides those.  Once [external_status] carries
     negative modes this becomes a lookup rather than a blanket refusal.
     A graph clause blocks unconditionally: its equations are exhaustive
     as a *definition*, which says nothing about the negative complement
     of any one mode, so no [Graph] relation may enter the complement
     table. *)
  fun clause_blocks_complement members external
        ({body, ...} : keyed_clause) =
    case body of
        GraphClause _ => true
      | HornClause {ordered, ...} =>
          List.exists (fn term =>
            case classify members external term of
                Prem _ => true
              | _ => false) ordered

  fun relation_blocks_complement members external clauses relation =
    List.exists (clause_blocks_complement members external)
      (clauses_for relation clauses)

  (* [strip_mode] is partial; a mode it cannot strip is simply not
     admitted.  Must use strict atomic-[Input] equality, not [given_mode]:
     this feeds the smart [Guard] complement, and a [Fun] component being
     "given" is not a claim that its failure is decidable.  The same
     strictness is what keeps a [Fixed] component out of the complement:
     [given_mode (Fixed _)] is true, [eq_mode (Fixed _, Input)] is not. *)
  fun mode_all_input mode =
    List.all (fn component => eq_mode (component, Input)) (strip_mode mode)
    handle Feedback.HOL_ERR _ => false

  (* Nothing may defer the decision: no [Prem] premise, no [Generator], no
     output position.  What is left is a finite chain of guards over ground
     inputs, whose failure is as decidable as its success, over a defining
     disjunction that is exact because no clause consults the fixpoint. *)
  fun negative_modes_of blocked modes =
    if blocked then []
    else List.mapPartial (fn (mode, _, needs_generator) =>
      if mode_all_input mode andalso not needs_generator
      then SOME mode else NONE) modes

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

  (* The module's one mode-inference fixpoint, over [relation_key]
     members: Horn SCCs ([infer_clauses]), a function's own graph
     ([infer_graph]), and a static-parameter re-run
     ([infer_fixed_argument]) all enter here.  [seed_modes] is the
     type-driven [all_modes_for_type o relation_type] except for
     [infer_fixed_argument], which narrows one relation's mode space to
     [Fixed value] at one position. *)
  fun infer_clauses_with seed_modes
        {members, clauses, external, reorder_premises} : inference_result =
    let
      (* [seed_modes] builds a member's whole mode space -- up to
         [max_mode_space] mode lists -- so it is computed once per
         member, here. *)
      val start = map (fn relation =>
        (relation, map (fn mode => (mode, [], false))
          (seed_modes relation))) members
      fun iteration table = map (fn (relation, modes) =>
        (relation, check_relation reorder_premises members external
          clauses table relation modes)) table
      fun fixpoint table =
        let val next = iteration table
        in if same_mode_table table next then next else fixpoint next end
      (* A member whose seed is [[]] -- a genuinely unsupported function
         parameter, or a mode space over [max_mode_space] -- stays [[]]
         through the fixpoint, since [check_relation] trivially returns
         [] for it every iteration. *)
      val stable = fixpoint start
      fun materialize (relation, modes) : relation_modes =
        {relation = relation, modes = modes}
      fun materialize_negative (relation, modes)
            : relation_negative_modes =
        {relation = relation,
         modes = negative_modes_of
           (relation_blocks_complement members external clauses relation)
           modes}
    in
      {relations = map materialize stable,
       negative = map materialize_negative stable}
    end

  (* A Horn clause is tagged with the constant its conclusion applies.
     A conclusion whose head is not a member's constant tags to a key no
     member carries, so [clauses_for] skips it -- exactly as the former
     head-matching filter did. *)
  fun horn_keyed_clause (clause : inference_clause) =
    {relation = Predicate (#1 (HolKernel.strip_comb (#head clause))),
     body = HornClause clause} : keyed_clause

  fun infer_clauses
        {members, clauses, external, reorder_premises} : inference_result =
    infer_clauses_with (all_modes_for_type o relation_type)
      {members = map Predicate members,
       clauses = map horn_keyed_clause clauses, external = external,
       reorder_premises = reorder_premises}

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
  fun scc_clauses members rules triple_for =
    let
      val clauses = List.mapPartial
        (clause_for_rule triple_for members) rules
    in
      if length clauses = length rules then SOME clauses else NONE
    end

  (* [f]'s graph is always exactly one self-recursive group, since
     [flatten_rhs] refuses any call to another function, so the fixpoint
     runs with a single member, no [external] table, and no cross-group
     reference to report.  [allow] is this module's sole
     [allow_function_inversion] gate -- with the flag off this returns
     [NONE] before [graph_clauses_for] is called, so no [Graph] key is
     built.  [NONE] also results from [graph_clauses_for] refusing the
     equations (unflattenable, non-exhaustive, or arity mismatch); this
     function raises no exception of its own, because [check_clause]'s
     blanket [HOL_ERR] handler already turns its live [split_arguments]
     raiser into a dropped mode.

     Reordering is the caller's [reorder_premises], for uniformity with
     the Horn path rather than for a difference it makes today: every
     shape [flatten_rhs] accepts yields at most one [GraphPrem] per
     clause, so the flag is unobservable here until it accepts a clause
     with two calls.  Probed over eleven library functions -- identical
     [inference_fingerprint] either way. *)
  fun infer_graph allow reorder_premises constant
        : inference_result option =
    if not allow then NONE
    else
      case graph_clauses_for constant of
          NONE => NONE
        | SOME clauses =>
            let
              val relation = Graph constant
            in
              SOME (infer_clauses_with (all_modes_for_type o relation_type)
                {members = [relation],
                 clauses = map (fn clause =>
                   {relation = relation,
                    body = GraphClause clause} : keyed_clause) clauses,
                 external = [], reorder_premises = reorder_premises})
            end

  (* Full beta normalization: [infer_fixed_argument] substitutes a closed
     value for a predicate parameter throughout a clause, which routinely
     leaves an un-reduced application of a literal lambda (e.g. [(\n. n =
     500) x]) sitting where a plain first-order guard belongs.  Reduce it
     away before mode inference ever sees the clause, rather than relying
     on a downstream validator: [Refute_Core.has_unexpanded_binder] does
     not reject a mere beta-redex (an [Abs] applied to an argument is not
     itself a forall/exists/select, and recursing into the [Abs]'s own
     body finds none either), and even where a check would degrade the
     compile safely, a clean substrate-neutral definition is what every
     substrate -- Cv's translator in particular -- should see. *)
  val beta_norm = Refute_Util.beta_normalize

  (* [Fixed]'s well-formedness guard, shared by the construction site
     and the API boundary below. *)
  fun fixed_position_ok relation position value =
    let
      val (domains, range) = boolSyntax.strip_fun (Term.type_of relation)
    in
      range = Type.bool andalso position >= 0 andalso
      position < length domains andalso
      null (Term.free_vars value) andalso
      Term.type_of value = List.nth (domains, position)
    end

  (* The mode space for [infer_fixed_argument]: every position keeps its
     ordinary [argument_modes] except [position], which is pinned to
     [Fixed value].  Never produced by [all_modes_for_type] itself, so
     the generic inference path is untouched.

     This is also the sole construction site for [Fixed]: an open value
     (one still carrying a free variable) is not merely wrong here, it is
     silently unsound downstream -- a [Fixed] position contributes to
     neither [ins] nor [outs], so the compiled enumerator would generate
     its own binding for that free variable, decoupled from the goal's,
     and report solutions to a premise the goal never asserted.  The
     closedness and type checks of [fixed_position_ok] are therefore
     load-bearing at this level, not a convenience; see
     [infer_fixed_argument] for the complementary, merely-defensive
     check at its own API boundary. *)
  fun fixed_modes_for relation position value =
    let
      val (domains, _) = boolSyntax.strip_fun (Term.type_of relation)
    in
      if not (fixed_position_ok relation position value) then []
      else
        let
          val per_position = Lib.mapi (fn index => fn domain =>
            if index = position then [Fixed value] else argument_modes domain)
            domains
          val total = List.foldl (fn (choices, count) =>
            let val width = Int.max (1, length choices)
            in
              if count > max_mode_space div width then max_mode_space + 1
              else count * width
            end) 1 per_position
        in
          if total <= max_mode_space then map list_mode (product per_position)
          else []
        end
    end
    handle Feedback.HOL_ERR _ => []

  (* Combine every option into [SOME] iff every element is [SOME]; the
     order-preserving analogue of [List.mapPartial] that must fail whole
     rather than silently drop a clause. *)
  fun sequence_options list =
    List.foldr (fn (item, acc) =>
      case (item, acc) of
          (SOME value, SOME rest) => SOME (value :: rest)
        | _ => NONE) (SOME []) list

  fun fixed_argument_target relation position
        ({head, ...} : inference_clause) =
    let val (head_relation, arguments) = HolKernel.strip_comb head
    in
      if same_constant head_relation relation then
        SOME (List.nth (arguments, position))
      else NONE
    end
    handle Feedback.HOL_ERR _ => NONE
         | Subscript => NONE

  (* [var = closed]/[closed = var], [closed] having no free variable at
     all: an occurs check is therefore unnecessary, [var] cannot appear
     inside its own [closed] value. *)
  fun ground_equality term =
    case Lib.total boolSyntax.dest_eq term of
        SOME (left, right) =>
          if Term.is_var left andalso null (Term.free_vars right) then
            SOME (left, right)
          else if Term.is_var right andalso null (Term.free_vars left) then
            SOME (right, left)
          else NONE
      | NONE => NONE

  (* Discharge every ground equality premise by substitution, dropping the
     premise and replacing the variable everywhere else in the clause --
     the same rewrite [Refute_QC]'s ordinary, non-smart planner already
     performs as its [try_eq] optimisation, applied here inside one
     clause instead of at plan level.  Fixing a predicate parameter to a
     literal like [\n. n = 500] routinely leaves exactly this shape behind
     ([x = 500] after beta reduction): without discharging it, the missing
     variable [x] can only be produced by [check_clause]'s blanket
     [Generator], turning a single baked-in value into a full runtime
     search over its whole type.  Discharging it here instead bakes [500]
     directly into the clause's own head (e.g. [x::xs] becomes [500::xs]),
     so the compiled enumerator constructs the witness rather than
     searching for it -- the cost this pays for is independent of how
     large the fixed value is.  Restricted to [substitute_fixed_argument]:
     ordinary, non-[Fixed] clauses are unaffected, so no other relation's
     already-pinned mode table can change shape by this.

     Every substitution below is wrapped in [beta_norm], exactly as
     [substitute_fixed_argument]'s own two substitutions are: this
     function's own [ground_equality] guard admits a function-typed
     [variable] equal to a closed lambda just as readily as a
     first-order one, and if that variable is itself applied elsewhere
     in the clause, a bare [Term.subst] would leave an un-reduced
     redex sitting in a clause body -- exactly what [beta_norm]'s own
     comment says must not reach the substrates.  No natural clause in
     the test zoo has been found that reaches this arm (it would need a
     clause-local, already-quantified predicate variable equated to a
     literal closed lambda rather than simply being written to that
     literal directly), so this is a defensive normalisation with no
     observed behaviour change, not a change guarded by a regression
     pin. *)
  fun discharge_ground_equalities (head, remaining) =
    case List.find (fn term => Option.isSome (ground_equality term))
           remaining of
        NONE => (head, remaining)
      | SOME equality =>
          let
            val (variable, value) = Option.valOf (ground_equality equality)
            val theta = [{redex = variable, residue = value}]
            val rest = List.filter (fn term => not (same_term term equality))
              remaining
          in
            discharge_ground_equalities
              (beta_norm (Term.subst theta head),
               map (beta_norm o Term.subst theta) rest)
          end

  (* A clause belonging to [relation] is rewritten iff its own occurrence
     of the parameter at [position] is a bare variable: only then does
     substituting [value] for it stand for "every call this clause makes
     is at [value]", rather than for some other, unrelated term that
     happens to sit there.  A clause belonging to any other member of the
     group is passed through unchanged; [Term.subst] on it would be a
     no-op regardless, since the variable being fixed is scoped to
     [relation]'s own clauses. *)
  fun substitute_fixed_argument relation position value
        (clause as {head, ordered, ...} : inference_clause) =
    case fixed_argument_target relation position clause of
        NONE => SOME clause
      | SOME target =>
          if Term.is_var target then
            let
              val theta = [{redex = target, residue = value}]
              val head' = beta_norm (Term.subst theta head)
              val ordered' = map (beta_norm o Term.subst theta) ordered
              val (head'', ordered'') =
                discharge_ground_equalities (head', ordered')
              (* Honest split, not [{side = [], main = ordered''}]: a
                 discharged ground equality drops out entirely, but a
                 premise that survives substitution without mentioning
                 [relation] at all (e.g. a residual arithmetic guard on
                 the substituted variable) is [side] under the very
                 invariant this record documents, not [main]. *)
              val (main'', side'') =
                List.partition (mentions relation) ordered''
            in
              SOME ({side = side'', main = main'', head = head'',
                     ordered = ordered''} : inference_clause)
            end
          else NONE

  (* Static-parameter mode inference: as [infer_clauses], but with
     [relation]'s argument at [position] pinned to the one closed [value]
     throughout, rather than left as the opaque, uninvertible [Fun] mode
     [predicate_mode_of] would otherwise assign it.  Every clause whose
     head belongs to [relation] is rewritten by substituting [value] for
     that argument (declining -- [NONE] -- if any such clause does not
     hold a bare variable there, since substitution would not then mean
     what it is supposed to); every other clause is untouched.  The
     result is then mode-checked by exactly [check_clause]/[check_relation]
     as any other clause set, so a [Fixed] position that turns out not to
     compile (its guards need a constant or function the compiler cannot
     yet see, or the position does not actually let go of the higher-order
     parameter) simply drops out of the fixpoint as usual: no separate
     success test is needed here beyond the ordinary one.
     Restricted to a Boolean-valued constant relation, a [position] inside
     its domain list, and a closed [value] of the matching type -- outside
     that, [NONE], the same safe degradation as every other inference
     entry point.

     The soundness-critical half of this guard (closedness, the type
     match) is enforced again, independently, at [fixed_modes_for] --
     the sole construction site for [Fixed] -- so this level cannot be
     bypassed by some other, future caller of that function.  Checking
     it here as well is this function's own API boundary: it lets a
     caller of [infer_fixed_argument] fail fast, before any clause
     substitution work, rather than only discovering the rejection once
     [fixed_modes_for] is reached below. *)
  fun infer_fixed_argument
        {members, clauses, external, reorder_premises, relation, position,
         value} =
    let
      val entry_ok = Term.is_const relation andalso
                     fixed_position_ok relation position value
    in
      if not entry_ok then NONE
      else
        case sequence_options
               (map (substitute_fixed_argument relation position value)
                 clauses) of
            NONE => NONE
          | SOME substituted =>
              (* Computed once: [infer_clauses_with] calls [seed_modes]
                 more than once per member, and each call rebuilds the
                 whole cartesian mode product. *)
              let val fixed = fixed_modes_for relation position value
              in
                if null fixed then NONE
                else
                  SOME (infer_clauses_with (fn candidate =>
                    if same_relation candidate (Predicate relation) then
                      fixed
                    else all_modes_for_type (relation_type candidate))
                    {members = map Predicate members,
                     clauses = map horn_keyed_clause substituted,
                     external = external,
                     reorder_premises = reorder_premises})
              end
    end
    handle Feedback.HOL_ERR _ => NONE
         | Subscript => NONE

  (* The substrate-neutral enumerator is a positive, depth-bounded CPS
     program.  [CpsClause] is [single inputs >>= case-match >>=
     premise-chain >>= single outputs]; the list of clauses is [plus] in
     source order.  Every substrate must preserve these two list orders. *)
  datatype cps_premise =
      CpsCall of {rel : relation_key, mode : mode, ins : term list,
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
  (* The cache and its generation are one mutable state: invalidation must
     not race a compilation publishing entries from the old generation. *)
  val enumerator_cache_mutex = Mutex.mutex ()
  fun synchronized_cache f =
    Multithreading.synchronized "Refute_SmartGen.enumerator_cache"
      enumerator_cache_mutex f

  abstype program_version = ProgramVersion of
    {generation : int, fingerprint : string}
  with
    val source_generation = ref 0

    fun same_program_version
          (ProgramVersion left, ProgramVersion right) = left = right

    fun current_program_version_raw
          (ProgramVersion {generation, ...}) =
      generation = !source_generation

    fun new_program_version fingerprint = ProgramVersion
      {generation = !source_generation, fingerprint = fingerprint}

    fun advance_source_generation () =
      source_generation := !source_generation + 1
  end

  type enumerator =
    {relation : relation_key, mode : mode, version : program_version,
     clauses : cps_clause list}

  fun first_order_mode (Fixed _) = true
    | first_order_mode Input = true
    | first_order_mode Output = true
    | first_order_mode (Pair (left, right)) =
        first_order_mode left andalso first_order_mode right
    | first_order_mode _ = false

  (* A relational premise compiles to the same call whether it is keyed
     by predicate or by function graph; only the key and how the
     arguments are obtained differ, so the first-order mode policy is
     stated once. *)
  fun compile_call key arguments derivation =
    (let
      val mode = head_mode_of derivation
      val (ins, outs) = split_arguments mode arguments
    in
      if List.all first_order_mode (strip_mode mode) then
        SOME (CpsCall {rel = key, mode = mode, ins = ins, outs = outs})
      else NONE
    end
    handle Feedback.HOL_ERR _ => NONE)

  fun compile_premise premise derivation =
    case premise of
        Generator variable => SOME (CpsGenerate variable)
      | Sidecond term => SOME (CpsGuard term)
      | Prem term =>
          let val (relation, arguments) = HolKernel.strip_comb term
          in compile_call (Predicate relation) arguments derivation end
      | GraphPrem (f, arguments) =>
          compile_call (Graph f) arguments derivation

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

  (* [compile_clause]'s [first_order_mode] check means no enumerator is
     ever compiled for a mode with a [Fun] component.  The drop is
     all-or-nothing at both stages: [check_relation] drops a mode
     entirely if any clause fails [check_clause], and [compile_relation]
     drops a mode entirely if any clause fails to compile. *)
  fun compile_relation version
        ({relation, modes} : relation_modes) =
    List.mapPartial (fn (mode, clauses, _) =>
      let val compiled = map (compile_clause mode) clauses
      in
        (* A dropped clause under-approximates the relation, and a
           zero-clause enumerator makes [negation_condition]
           unconditionally true. *)
        if List.all Option.isSome compiled then
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
        relation_string relation ^ "{" ^
        String.concatWith ";" (map (fn (mode, clauses, needs) =>
          mode_string mode ^ ":" ^ Bool.toString needs ^ ":" ^
          String.concatWith "/" (map clause clauses)) modes) ^ "}"
    in
      String.concatWith "|" (map relation relations)
    end

  type enumerator_cache_entry =
    {relation : relation_key, mode : mode, program : enumerator}

  (* Session-local only: enumerator compilation creates no HOL definition.
     Recompiling a typed relation/mode replaces its previous program. *)
  val enumerator_cache = ref ([] : enumerator_cache_entry list)

  fun same_enumerator_key relation mode
        ({relation = other, mode = other_mode, ...} :
          enumerator_cache_entry) =
    same_relation relation other andalso eq_mode (mode, other_mode)

  (* Retention is per (relation, mode), not per relation: a generic
     inference covers a relation's whole mode space, so a mode missing
     from a fresh result is dead and safe to drop, but a specialised
     inference (static-parameter specialisation) only ever covers the one
     mode it was asked for, so an absent mode there means nothing -- some
     other specialisation of the same relation may still hold the only
     copy of it.  A relation's clauses cannot change within one
     [source_generation], so a retained mode's program still matches them;
     [program_is_fresh]/[current_program_version_raw] handle staleness
     across generations regardless of how retention is keyed. *)
  fun cache_inference ({relations, ...} : inference_result) =
    let
      val version = synchronized_cache (fn () =>
        new_program_version (inference_fingerprint relations))
      val programs = List.concat (map (compile_relation version) relations)
      val fresh = map (fn program as {relation, mode, ...} =>
        {relation = relation, mode = mode, program = program}) programs
    in
      synchronized_cache (fn () =>
        if current_program_version_raw version then
          let val retained = List.filter (fn old =>
            not (List.exists (fn {relation, mode, ...} =>
              same_enumerator_key relation mode old) fresh))
            (!enumerator_cache)
          in enumerator_cache := fresh @ retained end
        else ())
    end

  fun program_is_fresh_unlocked ({relation, version, ...} : enumerator) =
    current_program_version_raw version andalso
    Theory.uptodate_term (relation_term relation)

  fun program_is_fresh program =
    synchronized_cache (fn () => program_is_fresh_unlocked program)

  fun enumerator_for_with is_fresh entries relation mode =
    case List.find (same_enumerator_key relation mode) entries of
        SOME {program, ...} =>
          if is_fresh program then SOME program else NONE
      | NONE => NONE

  fun enumerator_for_in entries relation mode =
    enumerator_for_with program_is_fresh entries relation mode

  fun enumerator_for relation mode =
    synchronized_cache (fn () =>
      enumerator_for_with program_is_fresh_unlocked (!enumerator_cache)
        relation mode)

  (* A compile invocation takes this immutable value once.  Code extraction
     must resolve the complete recursive closure from that value, never from
     the mutable session cache. *)
  fun enumerator_snapshot () =
    synchronized_cache (fn () =>
      List.filter (program_is_fresh_unlocked o #program) (!enumerator_cache))

  fun enumerator_gen_types ({clauses, ...} : enumerator) =
    List.concat (map (fn CpsClause {premises, ...} =>
      List.mapPartial (fn CpsGenerate variable =>
        SOME (Term.type_of variable) | _ => NONE) premises) clauses)

  (* The evaluator brackets its own definitions and cv translations in a
     theory snapshot/revert.  Those deltas say nothing about the relations
     enumerators were inferred from: every constant the bracket adds is
     private and freshly named, and the revert restores the baseline
     exactly.  Retiring the cache on them loses programs a plan has
     already promised -- planning records an Enum, the substrate then
     defines something, and the next substrate compiled from the same plan
     no longer finds the program.  Deltas are only ignored between
     [enter_private_theory] and the matching [leave_private_theory], and
     the evaluator holds HOL's single-mutator lock across exactly that
     span, so no user theory change can hide inside it. *)
  val private_theory_depth = ref 0

  fun enter_private_theory () =
    synchronized_cache (fn () =>
      private_theory_depth := !private_theory_depth + 1)

  fun leave_private_theory () =
    synchronized_cache (fn () =>
      private_theory_depth := Int.max (0, !private_theory_depth - 1))

  fun invalidate_enumerator_cache _ =
    synchronized_cache (fn () =>
      if !private_theory_depth > 0 then ()
      else (advance_source_generation (); enumerator_cache := []))

  val _ = Theory.register_hook
    ("Refute_SmartGen.enumerators", invalidate_enumerator_cache)

  fun relation_modes_for relation
        ({relations, ...} : inference_result) =
    List.find (fn ({relation = other, ...} : relation_modes) =>
      same_relation relation other) relations

  fun negative_relation_modes_for relation
        ({negative, ...} : inference_result) =
    List.find (fn ({relation = other, ...} : relation_negative_modes) =>
      same_relation relation other) negative

  (* The consumption test: may [relation]'s complement be compiled at
     [mode]? *)
  fun complement_available relation mode inference =
    case negative_relation_modes_for relation inference of
        NONE => false
      | SOME ({modes, ...} : relation_negative_modes) =>
          List.exists (fn other => eq_mode (other, mode)) modes

  fun top_level_parts mode arguments =
    SOME (split_arguments mode arguments)
    handle Feedback.HOL_ERR _ => NONE

  type goal_mode =
    {mode : mode, ins : term list, outs : term list,
     missing : term list, score : premise_score}

  (* Shared scoring body for both [Predicate] and [Graph] mode selection,
     using the same five-way order as rule mode inference.  Missing input
     variables are explicit: the plan compiler may generate them before
     the Enum, allowing an earlier equality premise to win and bind them
     instead when premise reordering is enabled.  Any route-specific
     policy over the resulting [outs] belongs at the call site, not here
     -- see [graph_mode_ok] below. *)
  fun modes_for_arguments known key arguments inference =
    let
      val relation_result = relation_modes_for key inference
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

  fun goal_modes_for_call known call inference =
    let val (relation, arguments) = HolKernel.strip_comb call
    in modes_for_arguments known (Predicate relation) arguments inference
    end
    handle Feedback.HOL_ERR _ => []

  (* [goal_modes_for_call]'s graph counterpart: [call] is not one term to
     [strip_comb] -- [constant]'s own type generally cannot accept the
     extra result argument -- so this takes the constant and the already
     flattened [a1 ... an, result] list directly, and looks up
     [Graph constant] instead of [Predicate relation].  Two policies apply
     only to a graph candidate, both enforced by [graph_mode_ok] after the
     shared scoring above: an all-input ([outs = []]) mode is refused, and
     every remaining [outs] entry must be a bare variable not already in
     [known] -- a graph-premise position is Input (every free variable
     already bound) or Output (a bare unbound variable), so a ground term
     or an already-bound variable sitting in [outs] (e.g. mode [(i,i,o)]
     against [xs ++ ys = zs] with [zs] already bound) is refused the same
     way.  Both matter for the same underlying reason.  A [Predicate]
     guard with no outputs still round-trips through [SmartGuard]: its
     stored [predicate] term IS the call, so [strip_comb] recovers the
     very same relation at lookup time.  An equation has no such
     round-trip -- [strip_comb (f a1 ... an = r)] yields [$=], not [f] --
     so a [Graph]-relation all-input candidate can never be found again by
     [smart_guard_lookup]; the consequence is not confined to that one
     candidate: [validate_plan] rejects the WHOLE plan on every substrate
     the moment one [SmartGuard] fails lookup, and Compute reaches that
     same rejection through [Refute_EvalEnum.prepare], never falling back
     to its own [eval_boolean] on the bare predicate.  A bound-variable or
     ground-term Output has a sharper cost: nothing there fails to
     compile, so an already-decided equation would plant an [Enum] where
     the ordinary route settles it exactly, a real loss of decisiveness
     even though sound.  Nothing is lost by excluding either shape here
     instead: the premise is already a plain checkable proposition,
     evaluated soundly by the ordinary route without any enumerator. *)
  fun graph_mode_ok known ({outs, ...} : goal_mode) =
    not (null outs) andalso
    List.all (fn out => Term.is_var out andalso not (member_term out known))
      outs

  fun graph_modes_for_call known constant arguments inference =
    List.filter (graph_mode_ok known)
      (modes_for_arguments known (Graph constant) arguments inference)

end
