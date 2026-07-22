structure Refute_Narrow = struct
  type hol_type = Type.hol_type
  type position = int list

  datatype narrowing_type =
    Narrowing_sum_of_products of narrowing_type list list

  datatype narrowing_term =
      Narrowing_variable of position * narrowing_type
    | Narrowing_constructor of int * narrowing_term list

  datatype shape_result =
      NarrowingShape of narrowing_type
    | Inapplicable of string list

  datatype evaluation =
      Known of {genuine : bool, result : bool}
    | NeedsRefinement of position

  type plain_test =
    { arguments : narrowing_term list,
      evaluate : bool -> narrowing_term list -> evaluation }

  datatype plain_result =
      PlainCounterexample of
        {genuine : bool, arguments : narrowing_term list, tests : int}
    | PlainExhausted of {tests : int}

  datatype plain_search_result =
      PlainFound of
        {depth : int, genuine : bool, arguments : narrowing_term list,
         tests : int}
    | PlainSearchExhausted of {tests : int}

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
    | Constructor of pnf_quantifier * truth * position * tree list

  datatype edge =
      V of position * narrowing_type
    | C of position * int

  type path = edge list

  datatype example =
      UnivExample of narrowing_term * example
    | ExExample of (narrowing_term * example) list
    | EmptyExample

  datatype pnf_result =
      PnfCounterexample of
        {genuine : bool, example : example, tree : tree, tests : int}
    | PnfExhausted of {truth : truth, tree : tree, tests : int}

  exception InvalidPosition of position
  exception InvalidPath
  exception NoUnevaluated
  exception ShapeFailure of hol_type * string

  fun products_of (Narrowing_sum_of_products products) = products

  (* Strict spine walks must apply a quantifier body to this value rather
     than to an undefined argument, as the lazy upstream engine does. *)
  fun dummy_variable position ty = Narrowing_variable (position, ty)

  fun non_empty (Narrowing_sum_of_products products) = not (null products)

  fun indexed_map f values =
    let
      fun loop _ [] = []
        | loop index (value :: rest) =
            f (index, value) :: loop (index + 1) rest
    in
      loop 0 values
    end

  (* This is Narrowing_Engine.new.  A child position is obtained by
     appending its product coordinate, not by allocating a fresh name. *)
  fun new position products =
    indexed_map (fn (constructor, argument_types) =>
      Narrowing_constructor
        (constructor,
         indexed_map (fn (index, ty) =>
           dummy_variable (position @ [index]) ty) argument_types))
      products

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
        new position (products_of ty)
    | refine (Narrowing_variable _) position =
        raise InvalidPosition position
    | refine (Narrowing_constructor (constructor, arguments)) position =
        List.map (fn refined =>
          Narrowing_constructor (constructor, refined))
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

  (* The first result is the minimal completion used for certification.
     Keeping the complete list is the strict transliteration of the
     upstream total operation and is useful when that first completion
     cannot be certified. *)
  fun total (Narrowing_constructor (constructor, arguments)) =
        List.map (fn completed =>
          Narrowing_constructor (constructor, completed))
          (cartesian (List.map total arguments))
    | total (Narrowing_variable (position, ty)) =
        List.concat (List.map total (new position (products_of ty)))

  fun flat_shape count =
    Narrowing_sum_of_products
      (List.tabulate (Int.max (0, count), fn _ => []))

  fun shape_failure ty reason = raise ShapeFailure (ty, reason)

  (* Shapes use the same depth convention as Quickcheck narrowing: nullary
     constructors remain available at depth zero, while every constructor
     argument consumes one level.  A constructor with an empty argument
     shape is itself omitted (the upstream "shallow" test). *)
  fun shape_of depth ty =
    let
      val depth = Int.max (0, depth)

      fun derive depth ty =
        case Refute_Gen.spec_of ty of
            Refute_Gen.GenEnum values => flat_shape (length values)
          | Refute_Gen.GenNum kind =>
              flat_shape (length (Refute_Gen.narrowing_terms kind depth))
          | Refute_Gen.GenDatatype {constrs, ...} =>
              let
                fun constructor_shape (_, []) = SOME []
                  | constructor_shape (_, argument_types) =
                      if depth = 0 then NONE
                      else
                        let
                          val argument_shapes =
                            List.map (derive (depth - 1)) argument_types
                        in
                          if List.all non_empty argument_shapes then
                            SOME argument_shapes
                          else
                            NONE
                        end
              in
                Narrowing_sum_of_products
                  (List.mapPartial constructor_shape constrs)
              end
          | Refute_Gen.GenFun _ =>
              shape_failure ty "function types require finitization"
          | Refute_Gen.GenCustom {enumerate = SOME enumerate, ...} =>
              flat_shape (length (enumerate depth))
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

  fun derive_shape depth ty =
    NarrowingShape (shape_of depth ty)
    handle ShapeFailure (offending_ty, reason) =>
      Inapplicable [inapplicable_message offending_ty reason]

  (* The plain Lazy SmallCheck engine.  The callback encapsulates forcing the
     extracted lazy property and translates Hole/Match into this first-order
     protocol.  Each refinement candidate is evaluated afresh, exactly as in
     Narrowing_Engine.ref/refute. *)
  fun refute_from genuine_only evaluate arguments tests =
    case evaluate genuine_only arguments of
        Known {genuine, result = true} => PlainExhausted {tests = tests + 1}
      | Known {genuine, result = false} =>
          PlainCounterexample
            {genuine = genuine, arguments = arguments, tests = tests + 1}
      | NeedsRefinement position =>
          let
            fun search [] count = PlainExhausted {tests = count}
              | search (refined :: rest) count =
                  (case refute_from genuine_only evaluate refined count of
                       result as PlainCounterexample _ => result
                     | PlainExhausted {tests = count'} =>
                         search rest count')
          in
            search (refineList arguments position) (tests + 1)
          end

  fun refute_plain genuine_only ({arguments, evaluate} : plain_test) =
    refute_from genuine_only evaluate arguments 0

  (* The upstream ML driver retries a potential hit genuinely at the next
     depth and discards it if the inclusive 0..size search finds no genuine
     hit. *)
  fun search_plain {size, genuine_only, at_depth} =
    let
      val maximum = size

      fun loop depth genuine_only tests =
        if depth > maximum then
          PlainSearchExhausted {tests = tests}
        else
          case refute_plain genuine_only (at_depth depth) of
              PlainExhausted {tests = count} =>
                loop (depth + 1) genuine_only (tests + count)
            | PlainCounterexample
                {genuine = true, arguments, tests = count} =>
                PlainFound
                  {depth = depth, genuine = true, arguments = arguments,
                   tests = tests + count}
            | PlainCounterexample
                {genuine = false, tests = count, ...} =>
                loop (depth + 1) true (tests + count)
    in
      loop 0 genuine_only 0
    end

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
    | value_of (Constructor (_, result, _, _)) = result

  fun ball trees =
    List.foldl (fn (subtree, result) =>
      conj (result, value_of subtree))
      (Eval {result = true, potential = false}) trees

  fun bexists trees =
    List.foldl (fn (subtree, result) =>
      disj (result, value_of subtree))
      (Eval {result = false, potential = false}) trees

  fun position_of (V (position, _)) = position
    | position_of (C (position, _)) = position

  fun first_index predicate values =
    let
      fun loop _ [] = NONE
        | loop index (value :: rest) =
            if predicate value then SOME index
            else loop (index + 1) rest
    in
      loop 0 values
    end

  (* The operation is intentionally partial, as upstream: it is called only
     while the root cache is Unevaluated. *)
  fun find (Leaf Unevaluated) = []
    | find (Variable (_, _, position, ty, subtree)) =
        V (position, ty) :: find subtree
    | find (Constructor (_, _, position, subtrees)) =
        (case first_index
           (fn subtree => value_of subtree = Unevaluated) subtrees of
             SOME index =>
               C (position, index) :: find (List.nth (subtrees, index))
           | NONE => raise NoUnevaluated)
    | find _ = raise NoUnevaluated

  fun update [] result (Leaf _) = Leaf result
    | update (V _ :: edges) result
        (Variable (quantifier, _, position, ty, subtree)) =
        let
          val subtree' = update edges result subtree
        in
          Variable
            (quantifier, value_of subtree', position, ty, subtree')
        end
    | update (C (_, index) :: edges) result
        (Constructor (quantifier, _, position, subtrees)) =
        let
          val subtree = List.nth (subtrees, index)
            handle Subscript => raise InvalidPath
          val subtree' = update edges result subtree
          val subtrees' = List.take (subtrees, index) @
            (subtree' :: List.drop (subtrees, index + 1))
          val aggregate =
            case quantifier of
                Universal => ball subtrees'
              | Existential => bexists subtrees'
        in
          Constructor (quantifier, aggregate, position, subtrees')
        end
    | update _ _ _ = raise InvalidPath

  fun replace_tree replacement [] subtree = replacement subtree
    | replace_tree replacement (V _ :: edges)
        (Variable (quantifier, result, position, ty, subtree)) =
        Variable
          (quantifier, result, position, ty,
           replace_tree replacement edges subtree)
    | replace_tree replacement (C (_, index) :: edges)
        (Constructor (quantifier, result, position, subtrees)) =
        let
          val subtree = List.nth (subtrees, index)
            handle Subscript => raise InvalidPath
          val subtree' = replace_tree replacement edges subtree
        in
          Constructor
            (quantifier, result, position,
             List.take (subtrees, index) @
               (subtree' :: List.drop (subtrees, index + 1)))
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
              (quantifier, result, position,
               Narrowing_sum_of_products products, subtree)) =
            let
              fun branch argument_types =
                List.foldr (fn ((index, ty), rest) =>
                  Variable
                    (quantifier, result, position @ [index], ty, rest))
                  subtree (indexed_map I argument_types)
            in
              Constructor
                (quantifier, result, position, List.map branch products)
            end
        | refine_variable _ = raise InvalidPath
    in
      replace_tree refine_variable (before_critical edges) tree
    end

  fun map_edge_position transform (V (position, ty)) =
        V (transform position, ty)
    | map_edge_position transform (C (position, index)) =
        C (transform position, index)

  fun tail_position (_ :: rest) = rest
    | tail_position [] = raise InvalidPath

  fun term_of position (C ([], constructor) :: edges) =
        Narrowing_constructor (constructor, terms_of position edges)
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

  (* Every quantified shape is made at this loop depth.  In particular there
     is no PNF-only generator depth constant. *)
  fun tree_of_types depth prefix =
    tree_of (List.map (fn (quantifier, ty) =>
      (quantifier, shape_of depth ty)) prefix)

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
        (terms, Constructor (quantifier, result, position, subtrees)) =
        if is_prefix prefix position then
          let
            val index =
              case first_index (is_false o value_of) subtrees of
                  SOME index => index
                | NONE => raise InvalidPath
            val selected = List.nth (subtrees, index)
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
            (terms @ [Narrowing_constructor (index, arguments)], residual)
          end
        else
          (terms,
           Constructor (quantifier, result, position, subtrees))

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
        (terms, Constructor (quantifier, result, position, subtrees)) =
        if is_prefix prefix position then
          let
            val indexed = indexed_map I subtrees
            val false_subtrees = List.filter
              (fn (_, subtree) => is_false (value_of subtree)) indexed

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

            fun extract (index, subtree) =
              List.map (fn (arguments, residual) =>
                (terms @ [Narrowing_constructor (index, arguments)],
                 residual))
                (fixpoint 0 ([], subtree))
          in
            List.concat (List.map extract false_subtrees)
          end
        else
          [(terms,
            Constructor (quantifier, result, position, subtrees))]

  fun quantifier_of (Variable (quantifier, _, _, _, _)) = quantifier
    | quantifier_of (Constructor (quantifier, _, _, _)) = quantifier
    | quantifier_of (Leaf _) = raise InvalidPath

  fun example_of _ (Leaf _) = EmptyExample
    | example_of index tree =
        case quantifier_of tree of
            Universal =>
              (case termlist_of [index] ([], tree) of
                   ([term], residual) =>
                     UnivExample (term, example_of (index + 1) residual)
                 | _ => raise InvalidPath)
          | Existential =>
              ExExample (List.map (fn (terms, residual) =>
                case terms of
                    [term] => (term, example_of (index + 1) residual)
                  | _ => raise InvalidPath)
                (alltermlist_of [index] ([], tree)))

  (* Keep the executable-spec spelling available to make audits against the
     Haskell extraction routine direct. *)
  val exampleOf = example_of

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

  fun apply_conversion conversion tm =
    (#2 (boolSyntax.dest_eq (Thm.concl (conversion tm))))
    handle UNCHANGED => tm

  fun prenex tm =
    let
      fun normalize tm =
        let
          val reduced = apply_conversion (DEPTH_CONV BETA_CONV) tm
          val rewritten = apply_conversion
            (Ho_Rewrite.REWRITE_CONV prenex_rewrites) reduced
        in
          if Term.aconv tm rewritten then rewritten
          else normalize rewritten
        end
    in
      normalize tm
    end

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

  fun pnf_problem tm =
    let val (prefix, body) = pnf_of tm
    in Refute_Eval.Pnf {prefix = prefix, body = body} end

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
