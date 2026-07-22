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
end
