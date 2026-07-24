structure Refute_Narrow = struct
  type hol_type = Type.hol_type
  type position = int list

  (* Alternative IDs are local to one immutable shape.  Exact enumerated
     values live only in meta-level shapes; narrowing terms carry local IDs.
     Per-compile reconstruction selects the corresponding frozen shape, so
     no process-global custom-term table retains HOL terms. *)
  datatype narrowing_type =
    Narrowing_sum_of_products of
      {depth : int, complete : bool, syntactic_complete : bool,
       alternatives : narrowing_alternative list}
  withtype narrowing_alternative =
    {id : int, exact : Term.term option, arguments : narrowing_type list}

  datatype narrowing_term =
      Narrowing_variable of position * narrowing_type
    | Narrowing_constructor of int * narrowing_term list

  datatype evaluation =
      Known of {genuine : bool, result : bool}
    | NeedsRefinement of position

  datatype plain_result =
      PlainCounterexample of
        {genuine : bool, arguments : narrowing_term list, tests : int}
    | PlainExhausted of {tests : int}

  datatype engine_selection =
      PlainEngine
    | PnfEngine
    | PlainRefusal of string list

  datatype pnf_quantifier = Existential | Universal

  (* [potential] records that Match, rather than an ordinary Boolean
     result, contributed to this value.  Keeping it in every decided tree
     cache avoids the upstream PNF driver's potential-to-genuine collapse. *)
  datatype truth =
      Eval of {result : bool, potential : bool}
    | Unevaluated
    | Unknown

  datatype tree =
      Leaf of truth
    | Variable of
        pnf_quantifier * truth * position * narrowing_type * tree
    | Constructor of
        pnf_quantifier * truth * position * narrowing_type *
        (int * tree) list

  datatype edge =
      V of position * narrowing_type
    | C of position * int * int

  type path = edge list

  datatype example =
      UnivExample of narrowing_type * narrowing_term * example
    | ExExample of
        narrowing_type * (narrowing_term * example) list
    | EmptyExample

  datatype pnf_result =
      PnfCounterexample of
        {genuine : bool, example : example, tree : tree, tests : int}
    | PnfExhausted of {truth : truth, tree : tree, tests : int}

  exception InvalidPosition of position
  exception InvalidPath
  exception NoUnevaluated
  exception ShapeFailure of hol_type * string

  fun products_of
        (Narrowing_sum_of_products {alternatives, ...}) = alternatives

  fun shape_complete
        (Narrowing_sum_of_products {complete, ...}) = complete

  fun shape_syntactically_complete
        (Narrowing_sum_of_products {syntactic_complete, ...}) =
    syntactic_complete

  fun shape_depth (Narrowing_sum_of_products {depth, ...}) = depth

  (* Strict spine walks must apply a quantifier body to this value rather
     than to an undefined argument, as the lazy upstream engine does. *)
  fun dummy_variable position ty = Narrowing_variable (position, ty)

  fun non_empty shape = not (null (products_of shape))

  (* Tupled view of [Lib.mapi], matching the (index, value) idiom the
     engine uses for product coordinates. *)
  fun indexed_map f values = Lib.mapi (Lib.curry f) values

  fun indexed_alternative (id, arguments) : narrowing_alternative =
    {id = id, exact = NONE, arguments = arguments}

  fun exact_alternative (id, value) : narrowing_alternative =
    {id = id, exact = SOME value, arguments = []}

  fun alternative_of shape id =
    case List.find (fn alternative => #id alternative = id)
      (products_of shape) of
        SOME alternative => alternative
      | NONE => raise InvalidPath

  (* This is Narrowing_Engine.new.  A child position is obtained by
     appending its product coordinate, not by allocating a fresh name. *)
  fun new position shape =
    List.map (fn alternative =>
      Narrowing_constructor
        (#id alternative,
         indexed_map (fn (index, ty) =>
           dummy_variable (position @ [index]) ty)
           (#arguments alternative)))
      (products_of shape)

  fun replace_nth values index replacements =
    let
      fun loop _ [] = raise InvalidPosition [index]
        | loop 0 (_ :: rest) =
            List.map (fn replacement => replacement :: rest) replacements
        | loop remaining (value :: rest) =
            List.map (fn tail => value :: tail)
              (loop (remaining - 1) rest)
    in
      if index < 0 then raise InvalidPosition [index]
      else loop index values
    end

  fun refine (Narrowing_variable (position, ty)) [] =
        new position ty
    | refine (Narrowing_variable _) position =
        raise InvalidPosition position
    | refine (Narrowing_constructor (id, arguments)) position =
        List.map (fn refined => Narrowing_constructor (id, refined))
          (refineList arguments position)

  and refineList arguments (index :: position) =
        replace_nth arguments index
          (refine (List.nth (arguments, index)) position
           handle Subscript => raise InvalidPosition (index :: position))
    | refineList _ [] = raise InvalidPosition []

  fun cartesian [] = [[]]
    | cartesian (values :: rest) =
        List.concat (List.map (fn value =>
          List.map (fn tail => value :: tail) (cartesian rest)) values)

  (* Grounding needs only the lexicographically first completion.  Upstream
     enumerates all of them (Narrowing_Engine.hs:27-29) and takes the head,
     which is free under Haskell's laziness and catastrophic under Poly/ML's
     strictness -- even char # char # char builds 256^3 terms first.  So the
     complete enumeration is not part of the engine at all; it lives in
     selftest.sml as the reference this function is checked against. *)
  fun first_completion shape term =
    let
      fun complete current_shape
            (Narrowing_constructor (id, arguments)) =
            let
              val alternative = alternative_of current_shape id
            in
              Option.map (fn completed =>
                Narrowing_constructor (id, completed))
                (complete_arguments
                  (#arguments alternative) arguments)
            end
        | complete _
            (Narrowing_variable (position, variable_shape)) =
            (case products_of variable_shape of
                 [] => NONE
               | alternative :: _ =>
                   complete variable_shape
                     (Narrowing_constructor
                       (#id alternative,
                        indexed_map (fn (index, ty) =>
                          dummy_variable (position @ [index]) ty)
                          (#arguments alternative))))

      and complete_arguments [] [] = SOME []
        | complete_arguments (shape :: shapes) (argument :: arguments) =
            (case complete shape argument of
                 NONE => NONE
               | SOME completed =>
                   Option.map (fn rest => completed :: rest)
                     (complete_arguments shapes arguments))
        | complete_arguments _ _ = raise InvalidPath
    in
      complete shape term
    end

  fun flat_shape depth complete values =
    Narrowing_sum_of_products
      {depth = depth, complete = complete,
       syntactic_complete = complete,
       alternatives = indexed_map exact_alternative values}

  fun shape_failure ty reason = raise ShapeFailure (ty, reason)

  fun is_finitization_approximation ty =
    case Lib.total Type.dest_thy_type ty of
        SOME {Thy = "refute", Tyop, ...} =>
          Tyop = "cfun" orelse Tyop = "ffun"
      | _ => false

  (* Shapes use the same depth convention as Quickcheck narrowing: nullary
     constructors remain available at depth zero, while every constructor
     argument consumes one level.  A constructor with an empty argument
     shape is itself omitted (the upstream "shallow" test). *)
  fun shape_of depth ty =
    let
      val depth = Int.max (0, depth)

      (* A constructor with several recursive arguments makes [derive] visit
         the same (depth, type) pair once per argument, so the naive walk is
         exponential in the depth.  A shape depends on nothing but that pair,
         so one cache per call collapses it. *)
      fun key_compare ((depth1, ty1), (depth2, ty2)) =
        case Int.compare (depth1, depth2) of
            EQUAL => Type.compare (ty1, ty2)
          | order => order
      val derived = ref (Redblackmap.mkDict key_compare)

      fun derive depth ty =
        case Redblackmap.peek (!derived, (depth, ty)) of
            SOME shape => shape
          | NONE =>
              let val shape = compute_shape depth ty
              in
                derived := Redblackmap.insert (!derived, (depth, ty), shape);
                shape
              end

      and compute_shape depth ty =
        case Refute_Gen.spec_of ty of
            Refute_Gen.GenEnum values => flat_shape depth true values
          | Refute_Gen.GenNum kind =>
              flat_shape depth false
                (Refute_Gen.narrowing_terms kind depth)
          | Refute_Gen.GenDatatype {constrs, ...} =>
              let
                fun constructor_shape
                      (index, (_, [])) =
                      SOME (indexed_alternative (index, []))
                  | constructor_shape
                      (index, (_, argument_types)) =
                      if depth = 0 then NONE
                      else
                        let
                          val argument_shapes =
                            List.map (derive (depth - 1)) argument_types
                        in
                          if List.all non_empty argument_shapes then
                            SOME
                              (indexed_alternative (index, argument_shapes))
                          else
                            NONE
                        end
                val alternatives = List.mapPartial constructor_shape
                  (indexed_map I constrs)
                val syntactic_complete =
                  length alternatives = length constrs andalso
                  List.all
                    (List.all shape_syntactically_complete o #arguments)
                    alternatives
                (* ffun and cfun enumerate datatype descriptions, not all
                   inhabitants of the source function type.  This semantic
                   incompleteness propagates through products and other
                   containing datatypes via their argument shapes. *)
                val complete =
                  syntactic_complete andalso
                  not (is_finitization_approximation ty) andalso
                  List.all (List.all shape_complete o #arguments)
                    alternatives
              in
                Narrowing_sum_of_products
                  {depth = depth, complete = complete,
                   syntactic_complete = syntactic_complete,
                   alternatives = alternatives}
              end
          | Refute_Gen.GenFun _ =>
              shape_failure ty "function types require finitization"
          | Refute_Gen.GenCustom {enumerate = SOME enumerate, ...} =>
              let
                val values = enumerate depth
                val _ = if List.all (fn value =>
                    Type.compare (Term.type_of value, ty) = EQUAL) values
                  then ()
                  else shape_failure ty
                    "custom exhaustive enumeration returned a mistyped value"
              in
                (* A custom callback has no completeness contract. *)
                flat_shape depth false values
              end
          | Refute_Gen.GenCustom _ =>
              shape_failure ty
                "custom generator has no exhaustive enumeration"
    in
      derive depth ty
    end
    handle Refute_Gen.NoGenerator (offending_ty, reason) =>
      shape_failure offending_ty reason

  fun inapplicable_message ty reason =
    "narrowing is inapplicable for " ^ Parse.type_to_string ty ^
    ": " ^ reason

  fun is_ground (Narrowing_variable _) = false
    | is_ground (Narrowing_constructor (_, arguments)) =
        List.all is_ground arguments

  fun all_ground arguments = List.all is_ground arguments

  fun first_variable_position arguments =
    let
      fun in_term (Narrowing_variable (position, _)) = SOME position
        | in_term (Narrowing_constructor (_, children)) = in_terms children
      and in_terms [] = NONE
        | in_terms (term :: terms) =
            (case in_term term of
                 SOME position => SOME position
               | NONE => in_terms terms)
    in
      in_terms arguments
    end

  (* The plain Lazy SmallCheck engine.  The callback encapsulates forcing the
     extracted lazy property and translates Hole/Match into this first-order
     protocol.  Each refinement candidate is evaluated afresh, exactly as in
     Narrowing_Engine.ref/refute.  Rejected hits are refined in this DFS;
     returning them to the driver as NONE would restart at the same root. *)
  fun refute_from genuine_only evaluate accept arguments tests =
    let
      fun search [] count = PlainExhausted {tests = count}
        | search (refined :: rest) count =
            (case refute_from genuine_only evaluate accept refined count of
                 result as PlainCounterexample _ => result
               | PlainExhausted {tests = count'} => search rest count')
      fun continue count =
        case first_variable_position arguments of
            NONE => PlainExhausted {tests = count}
          | SOME position => search (refineList arguments position) count
    in
      case evaluate genuine_only arguments of
          Known {genuine, result = true} =>
            PlainExhausted {tests = tests + 1}
        | Known {genuine, result = false} =>
            if accept arguments genuine then
              PlainCounterexample
                {genuine = genuine, arguments = arguments, tests = tests + 1}
            else
              continue (tests + 1)
        | NeedsRefinement position =>
            search (refineList arguments position) (tests + 1)
    end

  fun refute_plain_avoiding genuine_only
        {arguments, evaluate, accept} =
    refute_from genuine_only evaluate accept arguments 0

  (* Three-valued PNF refinement trees.  The Boolean tables are the upstream
     tables.  For decided values, potential tracks exactly the evidence needed
     for the result: conjunction needs every true result but only one false
     result, with disjunction dual. *)
  fun conj
        (Eval {result = false, potential = first},
         Eval {result = false, potential = second}) =
        Eval {result = false, potential = first andalso second}
    | conj (Eval {result = false, potential}, _) =
        Eval {result = false, potential = potential}
    | conj (_, Eval {result = false, potential}) =
        Eval {result = false, potential = potential}
    | conj
        (Eval {result = true, potential = first},
         Eval {result = true, potential = second}) =
        Eval {result = true, potential = first orelse second}
    | conj (Eval {result = true, ...}, other) = other
    | conj (other, Eval {result = true, ...}) = other
    | conj (Unevaluated, _) = Unevaluated
    | conj (_, Unevaluated) = Unevaluated
    | conj (Unknown, Unknown) = Unknown

  fun disj
        (Eval {result = true, potential = first},
         Eval {result = true, potential = second}) =
        Eval {result = true, potential = first andalso second}
    | disj (Eval {result = true, potential}, _) =
        Eval {result = true, potential = potential}
    | disj (_, Eval {result = true, potential}) =
        Eval {result = true, potential = potential}
    | disj
        (Eval {result = false, potential = first},
         Eval {result = false, potential = second}) =
        Eval {result = false, potential = first orelse second}
    | disj (Eval {result = false, ...}, other) = other
    | disj (other, Eval {result = false, ...}) = other
    | disj (Unknown, _) = Unknown
    | disj (_, Unknown) = Unknown
    | disj (Unevaluated, Unevaluated) = Unevaluated

  fun value_of (Leaf result) = result
    | value_of (Variable (_, result, _, _, _)) = result
    | value_of (Constructor (_, result, _, _, _)) = result

  fun ball branches =
    List.foldl (fn ((_, subtree), result) =>
      conj (result, value_of subtree))
      (Eval {result = true, potential = false}) branches

  fun incomplete_false shape
        (Eval {result = false, potential}) =
        Eval {result = false,
              potential = potential orelse not (shape_complete shape)}
    | incomplete_false _ truth = truth

  fun bexists shape branches =
    incomplete_false shape
      (List.foldl (fn ((_, subtree), result) =>
        disj (result, value_of subtree))
        (Eval {result = false, potential = false}) branches)

  fun variable_value Existential shape result =
        incomplete_false shape result
    | variable_value Universal _ result = result

  fun position_of (V (position, _)) = position
    | position_of (C (position, _, _)) = position

  fun first_index predicate values = Lib.total (Lib.index predicate) values

  (* The operation is intentionally partial, as upstream: it is called only
     while the root cache is Unevaluated. *)
  fun find (Leaf Unevaluated) = []
    | find (Variable (_, _, position, ty, subtree)) =
        V (position, ty) :: find subtree
    | find (Constructor (_, _, position, shape, branches)) =
        (case first_index
           (fn (_, subtree) => value_of subtree = Unevaluated) branches of
             SOME index =>
               let val (id, subtree) = List.nth (branches, index)
               in C (position, index, id) :: find subtree end
           | NONE => raise NoUnevaluated)
    | find _ = raise NoUnevaluated

  fun update [] result (Leaf _) = Leaf result
    | update (V _ :: edges) result
        (Variable (quantifier, _, position, ty, subtree)) =
        let
          val subtree' = update edges result subtree
        in
          Variable
            (quantifier, variable_value quantifier ty (value_of subtree'),
             position, ty, subtree')
        end
    | update (C (_, index, _) :: edges) result
        (Constructor (quantifier, _, position, shape, branches)) =
        let
          val (id, subtree) = List.nth (branches, index)
            handle Subscript => raise InvalidPath
          val subtree' = update edges result subtree
          val branches' = List.take (branches, index) @
            ((id, subtree') :: List.drop (branches, index + 1))
          val aggregate =
            case quantifier of
                Universal => ball branches'
              | Existential => bexists shape branches'
        in
          Constructor (quantifier, aggregate, position, shape, branches')
        end
    | update _ _ _ = raise InvalidPath

  fun replace_tree replacement [] subtree = replacement subtree
    | replace_tree replacement (V _ :: edges)
        (Variable (quantifier, result, position, ty, subtree)) =
        Variable
          (quantifier, result, position, ty,
           replace_tree replacement edges subtree)
    | replace_tree replacement (C (_, index, _) :: edges)
        (Constructor (quantifier, result, position, shape, branches)) =
        let
          val (id, subtree) = List.nth (branches, index)
            handle Subscript => raise InvalidPath
          val subtree' = replace_tree replacement edges subtree
        in
          Constructor
            (quantifier, result, position, shape,
             List.take (branches, index) @
               ((id, subtree') :: List.drop (branches, index + 1)))
        end
    | replace_tree _ _ _ = raise InvalidPath

  fun refine_tree edges critical_position tree =
    let
      fun before_critical [] = []
        | before_critical (edge :: rest) =
            if position_of edge = critical_position then []
            else edge :: before_critical rest

      fun refine_variable
            (Variable
              (quantifier, result, position, shape, subtree)) =
            let
              fun branch alternative =
                (#id alternative,
                 List.foldr (fn ((index, ty), rest) =>
                   Variable
                     (quantifier, result, position @ [index], ty, rest))
                   subtree (indexed_map I (#arguments alternative)))
            in
              Constructor
                (quantifier, result, position, shape,
                 List.map branch (products_of shape))
            end
        | refine_variable _ = raise InvalidPath
    in
      replace_tree refine_variable (before_critical edges) tree
    end

  fun map_edge_position transform (V (position, ty)) =
        V (transform position, ty)
    | map_edge_position transform (C (position, index, id)) =
        C (transform position, index, id)

  fun tail_position (_ :: rest) = rest
    | tail_position [] = raise InvalidPath

  fun term_of position (C ([], _, id) :: edges) =
        Narrowing_constructor (id, terms_of position edges)
    | term_of position [V ([], ty)] =
        Narrowing_variable (position, ty)
    | term_of _ _ = raise InvalidPath

  and terms_of position edges =
    let
      fun at_index index edge =
        case position_of edge of
            head :: _ => head = index
          | [] => raise InvalidPath

      fun loop _ [] = []
        | loop index remaining =
            let
              val (selected, rest) =
                List.partition (at_index index) remaining
              val stripped =
                List.map (map_edge_position tail_position) selected
            in
              term_of (position @ [index]) stripped ::
                loop (index + 1) rest
            end
    in
      loop 0 edges
    end

  fun tree_of prefix =
    let
      fun build _ [] = Leaf Unevaluated
        | build index ((quantifier, ty) :: rest) =
            Variable
              (quantifier, Unevaluated, [index], ty,
               build (index + 1) rest)
    in
      build 0 prefix
    end

  fun refute evaluate genuine_only depth initial_tree =
    let
      fun loop tree tests =
        let
          val path = find tree
          val tree' =
            case evaluate genuine_only (terms_of [] path) of
                Known {genuine, result} =>
                  update path
                    (Eval {result = result, potential = not genuine}) tree
              | NeedsRefinement position =>
                  if length position < depth then
                    refine_tree path position tree
                  else
                    update path Unknown tree
          val tests' = tests + 1
        in
          if value_of tree' = Unevaluated then loop tree' tests'
          else (tree', tests')
        end
    in
      loop initial_tree 0
    end

  fun is_false (Eval {result = false, ...}) = true
    | is_false _ = false

  fun is_genuine_false
        (Eval {result = false, potential = false}) = true
    | is_genuine_false _ = false

  fun is_prefix prefix position =
    length prefix <= length position andalso
    prefix = List.take (position, length prefix)

  fun termlist_of prefix (terms, Leaf result) =
        (terms, Leaf result)
    | termlist_of prefix
        (terms, Variable (quantifier, result, position, ty, subtree)) =
        if is_prefix prefix position then
          termlist_of prefix
            (terms @ [Narrowing_variable (position, ty)], subtree)
        else
          (terms,
           Variable (quantifier, result, position, ty, subtree))
    | termlist_of prefix
        (terms, Constructor (quantifier, result, position, shape, branches)) =
        if is_prefix prefix position then
          let
            val index =
              case first_index (is_genuine_false o value_of o #2) branches of
                  SOME index => index
                | NONE =>
                    (case first_index (is_false o value_of o #2) branches of
                         SOME index => index
                       | NONE => raise InvalidPath)
            val (id, selected) = List.nth (branches, index)
            fun fixpoint argument state =
              let
                val next =
                  termlist_of (position @ [argument]) state
              in
                if length (#1 next) = length (#1 state) then state
                else fixpoint (argument + 1) next
              end
            val (arguments, residual) = fixpoint 0 ([], selected)
          in
            (terms @ [Narrowing_constructor (id, arguments)], residual)
          end
        else
          (terms,
           Constructor (quantifier, result, position, shape, branches))

  fun alltermlist_of prefix (terms, Leaf result) =
        [(terms, Leaf result)]
    | alltermlist_of prefix
        (terms, Variable (quantifier, result, position, ty, subtree)) =
        if is_prefix prefix position then
          alltermlist_of prefix
            (terms @ [Narrowing_variable (position, ty)], subtree)
        else
          [(terms,
            Variable (quantifier, result, position, ty, subtree))]
    | alltermlist_of prefix
        (terms, Constructor (quantifier, result, position, shape, branches)) =
        if is_prefix prefix position then
          let
            val false_branches = List.filter
              (fn (_, subtree) => is_false (value_of subtree)) branches

            fun fixpoint argument state =
              let
                val next =
                  alltermlist_of (position @ [argument]) state
              in
                case next of
                    [single] =>
                      if length (#1 single) = length (#1 state) then
                        [single]
                      else
                        fixpoint (argument + 1) single
                  | many =>
                      List.concat (List.map
                        (fixpoint (argument + 1)) many)
              end

            fun extract (id, subtree) =
              List.map (fn (arguments, residual) =>
                (terms @ [Narrowing_constructor (id, arguments)], residual))
                (fixpoint 0 ([], subtree))
          in
            List.concat (List.map extract false_branches)
          end
        else
          [(terms,
            Constructor (quantifier, result, position, shape, branches))]

  fun quantifier_of (Variable (quantifier, _, _, _, _)) = quantifier
    | quantifier_of (Constructor (quantifier, _, _, _, _)) = quantifier
    | quantifier_of (Leaf _) = raise InvalidPath

  fun shape_of_tree (Variable (_, _, _, shape, _)) = shape
    | shape_of_tree (Constructor (_, _, _, shape, _)) = shape
    | shape_of_tree (Leaf _) = raise InvalidPath

  fun example_of _ (Leaf _) = EmptyExample
    | example_of index tree =
        case quantifier_of tree of
            Universal =>
              (case termlist_of [index] ([], tree) of
                   ([term], residual) =>
                     UnivExample
                       (shape_of_tree tree, term,
                        example_of (index + 1) residual)
                 | _ => raise InvalidPath)
          | Existential =>
              ExExample
                (shape_of_tree tree,
                 List.map (fn (terms, residual) =>
                   case terms of
                       [term] => (term, example_of (index + 1) residual)
                     | _ => raise InvalidPath)
                   (alltermlist_of [index] ([], tree)))

  (* Keep the executable-spec spelling available to make audits against the
     Haskell extraction routine direct. *)
  val exampleOf = example_of

  fun replay_shape shape =
    let
      fun project current =
        Refute_Eval.CaseShape
          {depth = shape_depth current,
           complete = shape_syntactically_complete current,
           constructors = map (fn alternative =>
             {id = #id alternative,
              fields = map project (#arguments alternative)})
             (products_of current)}
    in
      project shape
    end

  fun replay_pattern (Narrowing_variable _) = Refute_Eval.CaseVariable
    | replay_pattern (Narrowing_constructor (id, arguments)) =
        Refute_Eval.CaseConstructor (id, map replay_pattern arguments)

  fun replay_of_example rebuild example =
    let
      fun project _ EmptyExample = Refute_Eval.CaseLeaf
        | project index (UnivExample (shape, term, rest)) =
            Refute_Eval.CaseUniversal
              {shape = replay_shape shape,
               witness = rebuild index term,
               subtree = project (index + 1) rest}
        | project index (ExExample (shape, branches)) =
            Refute_Eval.CaseExistential
              {shape = replay_shape shape,
               branches = map (fn (term, rest) =>
                 (replay_pattern term, rebuild index term,
                  project (index + 1) rest)) branches}
    in
      project 0 example
    end

  (* Upstream reports a universal witness below existentials as a case term
     in the preceding existential variables.  Recreate that user-facing
     assignment from the replay tree; the tree itself remains the proof
     certificate consumed by Refute_Cert. *)
  fun case_bindings prefix tree =
    let
      fun at 0 ((Refute_Eval.Forall, _) :: _)
            (Refute_Eval.CaseUniversal {witness, ...}) = witness
        | at index ((Refute_Eval.Forall, _) :: rest)
            (Refute_Eval.CaseUniversal {subtree, ...}) =
            at (index - 1) rest subtree
        | at index ((Refute_Eval.Exists, variable) :: rest)
            (Refute_Eval.CaseExistential {branches, ...}) =
            TypeBase.mk_case
              (variable, map (fn (_, value, subtree) =>
                (value, at (index - 1) rest subtree)) branches)
        | at _ _ _ = raise InvalidPath

      fun collect _ [] = []
        | collect index ((quantifier, variable) :: rest) =
            (case quantifier of
                 Refute_Eval.Forall =>
                   (variable, at index prefix tree) ::
                   collect (index + 1) rest
               | Refute_Eval.Exists => collect (index + 1) rest)
    in
      collect 0 prefix
    end

  (* The universally closed goal puts its user frees before the original
     prefix.  Only those leading universal witnesses belong in [candidate.env];
     later existential branches are retained for proof replay. *)
  fun leading_universals 0 _ = []
    | leading_universals count (UnivExample (_, term, rest)) =
        term :: leading_universals (count - 1) rest
    | leading_universals _ _ = []

  fun refute_pnf genuine_only depth evaluate initial_tree =
    let
      val (tree, tests) =
        refute evaluate genuine_only depth initial_tree
    in
      case value_of tree of
          Eval {result = false, potential} =>
            PnfCounterexample
              {genuine = not potential, example = example_of 0 tree,
               tree = tree, tests = tests}
        | truth => PnfExhausted {truth = truth, tree = tree, tests = tests}
    end

  (* HOL4's pull theorems are the reversed all_simps/ex_simps family used by
     Isabelle's narrowing pass.  Ho_Rewrite handles binder renaming while the
     NOT rules expose quantifiers under negation. *)
  val prenex_rewrites =
    [ boolTheory.EQ_IMP_THM,
      boolTheory.EXISTS_UNIQUE_DEF,
      boolTheory.NOT_FORALL_THM,
      boolTheory.NOT_EXISTS_THM,
      boolTheory.LEFT_AND_FORALL_THM,
      boolTheory.RIGHT_AND_FORALL_THM,
      GSYM boolTheory.LEFT_EXISTS_AND_THM,
      GSYM boolTheory.RIGHT_EXISTS_AND_THM,
      GSYM boolTheory.LEFT_FORALL_OR_THM,
      GSYM boolTheory.RIGHT_FORALL_OR_THM,
      boolTheory.LEFT_OR_EXISTS_THM,
      boolTheory.RIGHT_OR_EXISTS_THM,
      GSYM boolTheory.LEFT_FORALL_IMP_THM,
      GSYM boolTheory.LEFT_EXISTS_IMP_THM,
      GSYM boolTheory.RIGHT_FORALL_IMP_THM,
      GSYM boolTheory.RIGHT_EXISTS_IMP_THM ]

  fun prenex_conversion tm =
    let
      fun step tm =
        let
          val beta =
            (DEPTH_CONV BETA_CONV tm
             handle UNCHANGED => Thm.REFL tm)
          val reduced = rhs_of beta
          val rewrite =
            (Ho_Rewrite.REWRITE_CONV prenex_rewrites reduced
             handle UNCHANGED => Thm.REFL reduced)
        in
          Thm.TRANS beta rewrite
        end

      fun normalize tm accumulated =
        let
          val next = step tm
          val rewritten = rhs_of next
          val accumulated' = Thm.TRANS accumulated next
        in
          if Term.aconv tm rewritten then accumulated'
          else normalize rewritten accumulated'
        end
    in
      normalize tm (Thm.REFL tm)
    end

  and rhs_of theorem = #2 (boolSyntax.dest_eq (Thm.concl theorem))

  fun prenex tm = rhs_of (prenex_conversion tm)

  fun strip_quantifiers tm =
    if boolSyntax.is_forall tm then
      let
        val (variable, body) = boolSyntax.dest_forall tm
        val (prefix, matrix) = strip_quantifiers body
      in
        ((Refute_Eval.Forall, variable) :: prefix, matrix)
      end
    else if boolSyntax.is_exists tm then
      let
        val (variable, body) = boolSyntax.dest_exists tm
        val (prefix, matrix) = strip_quantifiers body
      in
        ((Refute_Eval.Exists, variable) :: prefix, matrix)
      end
    else
      ([], tm)

  local
    fun pnf_of_closed tm = strip_quantifiers (prenex tm)
  in
    (* Free variables denote universally quantified test inputs.  Textual
       left-to-right order makes the public PNF entry deterministic. *)
    fun pnf_of tm =
      pnf_of_closed
        (boolSyntax.list_mk_forall (Term.free_vars_lr tm, tm))
  end

  fun ffun_type domain range =
    Type.mk_thy_type
      {Thy = "refute", Tyop = "ffun", Args = [domain, range]}

  fun cfun_type range =
    Type.mk_thy_type {Thy = "refute", Tyop = "cfun", Args = [range]}

  fun is_function_type ty = Option.isSome (Lib.total Type.dom_rng ty)

  fun is_product_type ty = Option.isSome (Lib.total pairSyntax.dest_prod ty)

  fun same_type left right = Type.compare (left, right) = EQUAL

  fun finitize_type ty =
    case Lib.total Type.dom_rng ty of
        SOME (domain, range) =>
          if is_function_type domain then cfun_type (finitize_type range)
          else ffun_type domain (finitize_type range)
      | NONE =>
          (case Lib.total pairSyntax.dest_prod ty of
               SOME (left, right) =>
                 pairSyntax.mk_prod
                   (finitize_type left, finitize_type right)
             | NONE => ty)

  fun mk_eval_ffun domain range =
    Term.mk_thy_const
      {Thy = "refute", Name = "eval_ffun",
       Ty = Type.-->(ffun_type domain range, Type.-->(domain, range))}

  fun mk_eval_cfun domain range =
    Term.mk_thy_const
      {Thy = "refute", Name = "eval_cfun",
       Ty = Type.-->(cfun_type range, Type.-->(domain, range))}

  (* Port of narrowing_generators.ML:finitize_functions.  The returned
     prefix carries only first-order datatype descriptions; [body] observes
     each description through eval_ffun/eval_cfun.  Products are mapped
     componentwise, as in upstream's map_prod branch. *)
  fun finitize_functions (prefix, body) =
    let
      fun transform ty =
        case Lib.total Type.dom_rng ty of
            SOME (domain, range) =>
              let
                val (range_ty, restore_range) = transform range
                val description_ty =
                  if is_function_type domain then cfun_type range_ty
                  else ffun_type domain range_ty
                val evaluator =
                  if is_function_type domain then
                    mk_eval_cfun domain range_ty
                  else
                    mk_eval_ffun domain range_ty
                fun restore description =
                  let
                    val argument = Term.variant
                      (Term.free_vars_lr description)
                      (Term.mk_var ("x", domain))
                    val result = Term.list_mk_comb
                      (evaluator, [description, argument])
                  in
                    Term.mk_abs (argument, restore_range result)
                  end
              in
                (description_ty, restore)
              end
          | NONE =>
              if is_product_type ty then
                let
                  val (left, right) = pairSyntax.dest_prod ty
                  val (left_ty, restore_left) = transform left
                  val (right_ty, restore_right) = transform right
                  fun restore description =
                    pairSyntax.mk_pair
                      (restore_left (pairSyntax.mk_fst description),
                       restore_right (pairSyntax.mk_snd description))
                in
                  (pairSyntax.mk_prod (left_ty, right_ty), restore)
                end
              else
                (ty, fn value => value)

      fun prepare ((quantifier, variable), avoid) =
        let
          val (ty, restore) = transform (Term.type_of variable)
          val replacement =
            if same_type ty (Term.type_of variable) then variable
            else Term.variant avoid
              (Term.mk_var (fst (Term.dest_var variable), ty))
        in
          ((quantifier, replacement),
           {redex = variable, residue = restore replacement},
           replacement :: avoid)
        end

      fun prepare_all [] _ entries substitutions =
            (rev entries, rev substitutions)
        | prepare_all (entry :: rest) avoid entries substitutions =
            let val (entry', substitution, avoid') = prepare (entry, avoid)
            in
              prepare_all rest avoid'
                (entry' :: entries) (substitution :: substitutions)
            end
      val (prefix', substitutions) =
        prepare_all prefix (Term.free_vars_lr body) [] []
    in
      (prefix', Term.subst substitutions body)
    end

  fun constructor_application expected term =
    let
      val (head, arguments) = HolKernel.strip_comb term
      val {Thy, Name, ...} = Term.dest_thy_const head
    in
      if Thy = "refute" andalso Name = expected then SOME arguments
      else NONE
    end
    handle HOL_ERR _ => NONE

  fun update_function point value base =
    Term.mk_comb (combinSyntax.mk_update (point, value), base)

  fun malformed_value expected value =
    raise Feedback.mk_HOL_ERR "Refute_Narrow"
      "eval_finite_functions_as"
      ("malformed transformed value for " ^ Parse.type_to_string expected ^
       ": " ^ Parse.term_to_string value)

  (* Reconstruct the original type as well as the original value.  Supplying
     that type is essential for cfun, whose datatype parameter deliberately
     omits the higher-order domain.  A narrowing variable may occur at every
     transformed node, so translate the marker before inspecting a datatype
     constructor. *)
  fun eval_finite_functions_as original_ty value =
    if not (same_type (Term.type_of value)
              (finitize_type original_ty)) then
      malformed_value original_ty value
    else if Refute_ModelFinder_Names.is_irrelevant_marker value then
      Refute_ModelFinder_Names.irrelevant_marker original_ty
    else
      case Lib.total Type.dom_rng original_ty of
          SOME (domain, range) =>
            if is_function_type domain then
              (case constructor_application "CConstant" value of
                   SOME [constant] =>
                     let
                       val argument =
                         Term.variant (Term.free_vars_lr constant)
                           (Term.mk_var ("x", domain))
                     in
                       Term.mk_abs
                         (argument,
                          eval_finite_functions_as range constant)
                     end
                 | _ => malformed_value original_ty value)
            else
              (case constructor_application "FConstant" value of
                   SOME [constant] =>
                     let
                       val argument =
                         Term.variant (Term.free_vars_lr constant)
                           (Term.mk_var ("x", domain))
                     in
                       Term.mk_abs
                         (argument,
                          eval_finite_functions_as range constant)
                     end
                 | _ =>
                     (case constructor_application "FUpdate" value of
                          SOME [point, result, rest] =>
                            update_function point
                              (eval_finite_functions_as range result)
                              (eval_finite_functions_as original_ty rest)
                        | _ => malformed_value original_ty value))
        | NONE =>
            if is_product_type original_ty then
              if pairSyntax.is_pair value then
                let
                  val (left_ty, right_ty) =
                    pairSyntax.dest_prod original_ty
                  val (left, right) = pairSyntax.dest_pair value
                in
                  pairSyntax.mk_pair
                    (eval_finite_functions_as left_ty left,
                     eval_finite_functions_as right_ty right)
                end
              else
                malformed_value original_ty value
            else
              value

  fun contains_existentials prefix =
    List.exists (fn (Refute_Eval.Exists, _) => true | _ => false) prefix

  fun select_engine allow_existentials prefix =
    if contains_existentials prefix then
      if allow_existentials then PnfEngine
      else PlainRefusal
        ["narrowing existential goals require allow_existentials"]
    else
      PlainEngine

  fun select_for_config (config : Refute_Core.config) tm =
    let val (prefix, body) = pnf_of tm
    in
      (select_engine (#allow_existentials (#qc config)) prefix,
       Refute_Eval.Pnf {prefix = prefix, body = body})
    end
end
