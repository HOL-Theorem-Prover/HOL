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

  exception InvalidPosition of position
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
