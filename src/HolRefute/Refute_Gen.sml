structure Refute_Gen = struct
  type term = Term.term
  type hol_type = Type.hol_type

  val enum_cap = 256

  datatype numkind = Num | Int | Char | Word of int

  type rng = Random.generator

  type custom_gen =
    { enumerate : (int -> term list) option,
      random : (int -> rng -> term) option }

  datatype genspec =
      GenDatatype of
        { constrs : (term * hol_type list) list,
          recursive : bool list list,
          min_size : int list list,
          family : hol_type list }
    | GenEnum of term list
    | GenNum of numkind
    | GenFun of hol_type * hol_type
    | GenCustom of custom_gen

  exception NoGenerator of hol_type * string

  val spec_cache : (hol_type, genspec) Redblackmap.dict ref =
    ref (Redblackmap.mkDict Type.compare)

  val cardinality_cache : (hol_type, int option) Redblackmap.dict ref =
    ref (Redblackmap.mkDict Type.compare)

  val enumerate_cache : (hol_type, term list option) Redblackmap.dict ref =
    ref (Redblackmap.mkDict Type.compare)

  val user_generators : (hol_type * custom_gen) list ref = ref []
  val abstract_specs : (hol_type * genspec) list ref = ref []
  val abstract_predicates : (hol_type * term) list ref = ref []

  fun same_type (ty1, ty2) = Type.compare (ty1, ty2) = EQUAL

  fun lookup_type entries ty =
    Option.map #2
      (List.find (fn (entry_ty, _) => same_type (entry_ty, ty)) entries)

  fun remove_type ty entries =
    List.filter (fn (entry_ty, _) => not (same_type (entry_ty, ty))) entries

  fun cached_spec ty = Redblackmap.peek (!spec_cache, ty)

  fun cache_spec ty spec =
    spec_cache := Redblackmap.insert (!spec_cache, ty, spec)

  fun invalidate_cache _ =
    (spec_cache := Redblackmap.mkDict Type.compare;
     cardinality_cache := Redblackmap.mkDict Type.compare;
     enumerate_cache := Redblackmap.mkDict Type.compare)

  val _ = Theory.register_hook
    ("Refute_Gen.spec_of", invalidate_cache)

  fun generator_of ty = lookup_type (!user_generators) ty

  fun predicate_of ty = lookup_type (!abstract_predicates) ty

  fun register_generator ty generator =
    case (#enumerate generator, #random generator) of
      (NONE, NONE) =>
        raise Fail "Refute_Gen.register_generator: empty generator"
    | _ =>
        (user_generators :=
           (ty, generator) :: remove_type ty (!user_generators)
         ; invalidate_cache ())

  fun dest_fun ty = Type.dom_rng ty

  fun word_kind ty =
    let
      val width = wordsSyntax.dest_word_type ty
    in
      SOME (Word (Arbnum.toInt (fcpLib.index_to_num width)))
    end
    handle Feedback.HOL_ERR _ => NONE

  fun numeric_kind ty =
    if same_type (ty, numSyntax.num) then SOME Num
    else if same_type (ty, intSyntax.int_ty) then SOME Int
    else if same_type (ty, stringSyntax.char_ty) then SOME Char
    else word_kind ty

  fun quotient_result_type th =
    let
      val (_, body) = boolSyntax.strip_forall (Thm.concl th)
      val (head, args) = boolSyntax.strip_comb body
      val {Thy, Name, ...} = Term.dest_thy_const head
      val _ =
        if Thy = "quotient" andalso Name = "QUOTIENT" then ()
        else raise Fail "not a quotient theorem"
      val abs = List.nth (args, 1)
    in
      SOME (#2 (dest_fun (Term.type_of abs)))
    end
    handle Feedback.HOL_ERR _ => NONE
         | Subscript => NONE
         | Fail _ => NONE

  fun quotient_types () =
    let
      val data = ThmSetData.current_data {settype = "quotient"}
    in
      List.mapPartial quotient_result_type (ThmSetData.added_thms data)
    end
    handle Feedback.HOL_ERR _ => []

  fun is_named_quotient ty =
    case Type.dest_type ty of
        ("real", []) => true
      | ("rat", []) => true
      | _ => false
    handle Feedback.HOL_ERR _ => false

  fun is_quotient_type ty =
    is_named_quotient ty orelse
    List.exists (fn quotient_ty => same_type (quotient_ty, ty))
      (quotient_types ())

  fun constructor_data ty info =
    let
      fun one constr =
        let
          val constr = TypeBasePure.cinst ty constr
          val (args, _) = boolSyntax.strip_fun (Term.type_of constr)
        in
          (constr, args)
        end
    in
      List.map one (TypeBasePure.constructors_of info)
    end

  fun induction_key info =
    case TypeBasePure.induction_of0 info of
      TypeBasePure.COPY (key, _) => key
    | TypeBasePure.ORIG _ => TypeBasePure.ty_name_of info

  fun same_family key info =
    case Lib.total TypeBasePure.induction_of0 info of
      NONE => false
    | SOME (TypeBasePure.COPY (other, _)) => other = key
    | SOME (TypeBasePure.ORIG _) => TypeBasePure.ty_name_of info = key

  fun family_of ty info =
    let
      val key = induction_key info
      val theta = Type.match_type (TypeBasePure.ty_of info) ty
      fun instantiate family_info =
        Type.type_subst theta (TypeBasePure.ty_of family_info)
    in
      List.map instantiate (List.filter (same_family key) (TypeBase.elts ()))
    end

  fun type_mentions family ty =
    if List.exists (fn family_ty => same_type (family_ty, ty)) family then
      true
    else if Type.is_vartype ty then
      false
    else
      List.exists (type_mentions family) (#2 (Type.dest_type ty))

  fun recursive_under_function family ty =
    let
      fun visit beneath ty =
        if List.exists (fn family_ty => same_type (family_ty, ty)) family
        then beneath
        else if Type.is_vartype ty then false
        else
          case Lib.total dest_fun ty of
            SOME (dom, rng) => visit true dom orelse visit true rng
          | NONE => List.exists (visit beneath) (#2 (Type.dest_type ty))
    in
      visit false ty
    end

  fun own_floor (GenDatatype {min_size, ...}) =
        List.foldl Int.min 1073741823
          (List.map (fn row => List.foldl Int.max 0 row) min_size)
    | own_floor _ = 0

  fun no_generator ty =
    NoGenerator (ty, "no TypeBase information; register a generator")

  fun spec_of ty =
    case generator_of ty of
      SOME generator => GenCustom generator
    | NONE =>
        (case lookup_type (!abstract_specs) ty of
           SOME spec => spec
         | NONE =>
    (case cached_spec ty of
      SOME spec => spec
    | NONE =>
        let
          fun floor_of family floors arg_ty =
            if Type.is_vartype arg_ty then 0
            else
              case List.find (fn (family_ty, _) =>
                same_type (family_ty, arg_ty)) floors of
                SOME (_, floor) => floor
              | NONE => own_floor (spec_of arg_ty)

          fun family_floors family =
            let
              fun floor_for floors family_ty =
                case TypeBase.fetch family_ty of
                  NONE => 0
                | SOME family_info =>
                    let
                      val constrs = constructor_data family_ty family_info
                      fun ctor_floor (_, args) =
                        if List.null args then 0
                        else
                          List.foldl Int.max 0
                            (List.map (fn arg_ty =>
                              if type_mentions family arg_ty then
                                (case List.find (fn (family_ty, _) =>
                                  same_type (family_ty, arg_ty)) floors of
                                   SOME (_, floor) => floor + 1
                                 | NONE => 1)
                              else
                                floor_of family floors arg_ty) args)
                    in
                      List.foldl Int.min 1073741823
                        (List.map ctor_floor constrs)
                    end

              fun improve floors =
                List.map (fn family_ty =>
                  (family_ty, floor_for floors family_ty)) family

              fun equal_floors ([], []) = true
                | equal_floors ((ty1, floor1) :: rest1,
                    (ty2, floor2) :: rest2) =
                    same_type (ty1, ty2) andalso floor1 = floor2 andalso
                    equal_floors (rest1, rest2)
                | equal_floors _ = false

              fun iterate 0 floors =
                let
                  val next = improve floors
                in
                  if equal_floors (floors, next) then next
                  else
                    raise NoGenerator
                      (ty,
                       "datatype has no finite value; register a generator")
                end
                | iterate remaining floors =
                let
                  val next = improve floors
                in
                  if equal_floors (floors, next) then next
                  else iterate (remaining - 1) next
                end
            in
              iterate (List.length family)
                (List.map (fn family_ty => (family_ty, 0)) family)
            end

          fun datatype_spec info =
            let
              val family = family_of ty info
              val floors = family_floors family
              val constrs = constructor_data ty info
              val recursive = List.map (fn (_, args) =>
                List.map (type_mentions family) args) constrs
              val _ =
                if List.exists (fn (_, args) =>
                  List.exists (recursive_under_function family) args) constrs
                then
                  raise NoGenerator
                    (ty,
                     "Creation of exhaustive generators failed because " ^
                     "the datatype is recursive under a function type")
                else
                  ()
              val min_size = List.map (fn (_, args) =>
                List.map (fn arg_ty =>
                  if type_mentions family arg_ty then
                    (case List.find (fn (family_ty, _) =>
                      same_type (family_ty, arg_ty)) floors of
                       SOME (_, floor) => floor + 1
                     | NONE => 1)
                  else
                    floor_of family floors arg_ty) args) constrs
            in
              if List.all (fn (_, args) => List.null args) constrs then
                GenEnum (List.map #1 constrs)
              else
                GenDatatype
                  { constrs = constrs,
                    recursive = recursive,
                    min_size = min_size,
                    family = family }
            end

          val spec =
            case numeric_kind ty of
              SOME kind => GenNum kind
            | NONE =>
                (case Lib.total dest_fun ty of
                   SOME (dom, rng) => GenFun (dom, rng)
                 | NONE =>
                     (case TypeBase.fetch ty of
                        SOME info => datatype_spec info
                      | NONE =>
                          if is_quotient_type ty then
                            raise NoGenerator
                              (ty, "quotient type; register a generator")
                          else
                            raise no_generator ty))
          val _ = cache_spec ty spec
        in
          spec
        end))

  fun result_type tm = #2 (boolSyntax.strip_fun (Term.type_of tm))

  fun abstract_generator {ty, constructors, pred} =
    let
      fun bad message =
        raise Fail ("Refute_Gen.abstract_generator: " ^ message)

      fun instantiate constructor =
        let
          val _ = if Term.is_const constructor then ()
                  else bad "constructors must be constants"
          val result_ty = result_type constructor
          val (_, result_args) = Type.dest_type result_ty
          val _ = if List.all Type.is_vartype result_args then ()
                  else bad ("constructor result must have type-variable " ^
                            "arguments")
          val theta = Type.match_type result_ty ty
          val constructor = Term.inst theta constructor
          val (args, actual_ty) =
            boolSyntax.strip_fun (Term.type_of constructor)
          val _ = if same_type (actual_ty, ty) then ()
                  else bad "constructor has a mismatching result type"
          val _ =
            if List.exists (recursive_under_function [ty]) args then
              bad "constructor is recursive under a function type"
            else
              ()
        in
          (constructor, args)
        end

      val _ =
        if List.null constructors then bad "constructors must be nonempty"
        else ()
      val constrs = List.map instantiate constructors
      val recursive = List.map (fn (_, args) =>
        List.map (type_mentions [ty]) args) constrs
      val min_size = List.map (fn row =>
        List.map (fn is_recursive => if is_recursive then 1 else 0) row)
          recursive
      val spec =
        GenDatatype
          { constrs = constrs,
            recursive = recursive,
            min_size = min_size,
            family = [ty] }
      val _ =
        case pred of
          NONE => ()
        | SOME predicate =>
            let
              val (dom, rng) = dest_fun (Term.type_of predicate)
            in
              if same_type (dom, ty) andalso same_type (rng, Type.bool)
              then ()
              else bad "predicate must have type ty -> bool"
            end
      val _ = abstract_specs := (ty, spec) :: remove_type ty (!abstract_specs)
      val _ =
        case pred of
          NONE =>
            abstract_predicates := remove_type ty (!abstract_predicates)
        | SOME predicate =>
            abstract_predicates :=
              (ty, predicate) :: remove_type ty (!abstract_predicates)
      val _ = invalidate_cache ()
    in
      ()
    end

  fun cap_product values =
    let
      fun multiply value total =
        if value < 0 orelse total < 0 orelse
           value > enum_cap div Int.max (1, total) then
          NONE
        else
          SOME (total * value)

      fun loop [] total = SOME total
        | loop (NONE :: _) _ = NONE
        | loop (SOME value :: rest) total =
            (case multiply value total of
               NONE => NONE
             | SOME next => loop rest next)
    in
      loop values 1
    end

  fun cap_sum values =
    let
      fun loop [] total = SOME total
        | loop (NONE :: _) _ = NONE
        | loop (SOME value :: rest) total =
            if value < 0 orelse value > enum_cap - total then NONE
            else loop rest (total + value)
    in
      loop values 0
    end

  fun cap_power base exponent =
    if exponent < 0 then NONE
    else cap_product (List.tabulate (exponent, fn _ => SOME base))

  fun int_power base exponent =
    let
      fun loop 0 total = total
        | loop remaining total = loop (remaining - 1) (base * total)
    in
      loop exponent 1
    end

  fun cardinality ty =
    case Redblackmap.peek (!cardinality_cache, ty) of
        SOME cached => cached
      | NONE =>
    let
      fun datatype_cardinality (constrs, recursive) =
        let
          fun one ((_, args), recursive_args) =
            if List.exists (fn flag => flag) recursive_args then NONE
            else cap_product (List.map cardinality args)

          fun rows ([], []) = []
            | rows (constr :: constrs, flags :: rest) =
                one (constr, flags) :: rows (constrs, rest)
            | rows _ = [NONE]
        in
          cap_sum (rows (constrs, recursive))
        end

      fun from_spec (GenEnum values) =
            if length values <= enum_cap then SOME (length values) else NONE
        | from_spec (GenNum Num) = NONE
        | from_spec (GenNum Int) = NONE
        | from_spec (GenNum Char) = SOME enum_cap
        | from_spec (GenNum (Word width)) = cap_power 2 width
        | from_spec (GenFun (dom, rng)) =
            (case (cardinality dom, cardinality rng) of
               (SOME dom_card, SOME rng_card) => cap_power rng_card dom_card
             | _ => NONE)
        | from_spec (GenDatatype {constrs, recursive, ...}) =
            datatype_cardinality (constrs, recursive)
        | from_spec (GenCustom _) = NONE
    in
      let
        val result = from_spec (spec_of ty) handle NoGenerator _ => NONE
      in
        cardinality_cache :=
          Redblackmap.insert (!cardinality_cache, ty, result);
        result
      end
    end

  fun choices 0 _ = [[]]
    | choices count values =
        List.concat (List.map (fn value =>
          List.map (fn rest => value :: rest) (choices (count - 1) values))
          values)

  fun term_products [] = SOME [[]]
    | term_products (NONE :: _) = NONE
    | term_products (SOME values :: rest) =
        (case term_products rest of
           NONE => NONE
         | SOME tails =>
             SOME (List.concat (List.map (fn value =>
               List.map (fn tail => value :: tail) tails) values)))

  fun enumerate ty =
    case Redblackmap.peek (!enumerate_cache, ty) of
        SOME cached => cached
      | NONE =>
    let
      fun word_terms width =
        List.tabulate (int_power 2 width, fn value =>
          wordsSyntax.mk_wordii (value, width))

      fun char_terms () =
        List.tabulate (enum_cap, fn value =>
          stringSyntax.mk_chr (numSyntax.term_of_int value))

      fun datatype_terms (constrs, recursive) =
        let
          fun one ((constructor, args), recursive_args) =
            if List.exists (fn flag => flag) recursive_args then NONE
            else
              case term_products (List.map enumerate args) of
                NONE => NONE
              | SOME arguments =>
                  SOME (List.map (fn terms =>
                    Term.list_mk_comb (constructor, terms)) arguments)

          fun rows ([], []) = SOME []
            | rows (constr :: constrs, flags :: rest) =
                (case (one (constr, flags), rows (constrs, rest)) of
                   (SOME values, SOME more) => SOME (values @ more)
                 | _ => NONE)
            | rows _ = NONE
        in
          rows (constrs, recursive)
        end

      fun function_terms (dom, rng) =
        case (enumerate dom, enumerate rng) of
          (SOME domain, SOME range) =>
            let
              val variable = Term.mk_var ("x", dom)
              val base = Term.mk_abs (variable, hd range)
              fun make_graph values =
                List.foldl (fn ((argument, value), graph) =>
                  Term.mk_comb (combinSyntax.mk_update (argument, value),
                    graph)) base (ListPair.zip (domain, values))
            in
              SOME (List.map make_graph (choices (length domain) range))
            end
        | _ => NONE

      fun from_spec (GenEnum values) = SOME values
        | from_spec (GenNum Num) = NONE
        | from_spec (GenNum Int) = NONE
        | from_spec (GenNum Char) = SOME (char_terms ())
        | from_spec (GenNum (Word width)) = SOME (word_terms width)
        | from_spec (GenFun types) = function_terms types
        | from_spec (GenDatatype {constrs, recursive, ...}) =
            datatype_terms (constrs, recursive)
        | from_spec (GenCustom _) = NONE
    in
      let
        val result =
          (case cardinality ty of
             NONE => NONE
           | SOME _ => from_spec (spec_of ty))
          handle NoGenerator _ => NONE
      in
        enumerate_cache :=
          Redblackmap.insert (!enumerate_cache, ty, result);
        result
      end
    end
end
