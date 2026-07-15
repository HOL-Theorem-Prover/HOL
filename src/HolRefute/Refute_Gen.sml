structure Refute_Gen = struct
  type term = Term.term
  type hol_type = Type.hol_type

  val enum_cap = 256

  datatype numkind = Num | Int | Char | Word of int

  (* TASK_06 replaces this with the executable custom-generator record. *)
  type custom_gen = unit

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

  type cache_key = string * string
  type cache_entry = cache_key * hol_type * genspec

  val spec_cache : cache_entry list ref = ref []

  fun type_key ty =
    if Type.is_vartype ty then ("", Type.dest_vartype ty)
    else
      let
        val {Thy, Tyop, ...} = Type.dest_thy_type ty
      in
        (Thy, Tyop)
      end

  fun same_type (ty1, ty2) = Type.compare (ty1, ty2) = EQUAL

  fun cached_spec ty =
    let
      fun find [] = NONE
        | find ((key, cached_ty, spec) :: rest) =
            if key = type_key ty andalso same_type (cached_ty, ty) then
              SOME spec
            else
              find rest
    in
      find (!spec_cache)
    end

  fun cache_spec ty spec =
    spec_cache := (type_key ty, ty, spec) :: !spec_cache

  fun invalidate_cache _ = spec_cache := []

  val _ = Theory.register_hook
    ("Refute_Gen.spec_of", invalidate_cache)

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

  fun is_quotient_type ty =
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
        List.foldl Int.min 0
          (List.map (fn row => List.foldl Int.max 0 row) min_size)
    | own_floor _ = 0

  fun no_generator ty =
    NoGenerator (ty, "no TypeBase information; register a generator")

  fun spec_of ty =
    case cached_spec ty of
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
        end
end
