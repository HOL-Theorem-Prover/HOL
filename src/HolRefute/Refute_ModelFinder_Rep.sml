signature REFUTE_MODEL_FINDER_REP = sig
  type polarity = Refute_ModelFinder_Util.polarity
  type hol_type = Type.hol_type
  type scope = Refute_ModelFinder_Scope.scope
  type offset_table = Refute_ModelFinder_Scope.offset_table

  datatype rep =
    Any
  | Formula of polarity
  | Atom of int * int
  | Struct of rep list
  | Vect of int * rep
  | Func of rep * rep
  | Opt of rep

  exception REP of string * rep list

  val string_for_polarity : polarity -> string
  val string_for_rep : rep -> string
  val is_Func : rep -> bool
  val is_Opt : rep -> bool
  val is_opt_rep : rep -> bool
  val flip_rep_polarity : rep -> rep
  val card_of_rep : rep -> int
  val arity_of_rep : rep -> int
  val min_univ_card_of_rep : rep -> int
  val is_one_rep : rep -> bool
  val is_lone_rep : rep -> bool
  val dest_Func : rep -> rep * rep
  val lazy_range_rep :
    offset_table -> hol_type -> (unit -> int) -> rep -> rep
  val binder_reps : rep -> rep list
  val body_rep : rep -> rep
  val one_rep : offset_table -> hol_type -> rep -> rep
  val optable_rep : offset_table -> hol_type -> rep -> rep
  val opt_rep : offset_table -> hol_type -> rep -> rep
  val unopt_rep : rep -> rep
  val min_rep : rep -> rep -> rep
  val min_reps : rep list -> rep list -> rep list
  val card_of_domain_from_rep : int -> rep -> int
  val rep_to_binary_rel_rep : offset_table -> hol_type -> rep -> rep
  val best_one_rep_for_type : scope -> hol_type -> rep
  val best_opt_set_rep_for_type : scope -> hol_type -> rep
  val best_non_opt_set_rep_for_type : scope -> hol_type -> rep
  val best_set_rep_for_type : scope -> hol_type -> rep
  val atom_schema_of_rep : rep -> (int * int) list
  val atom_schema_of_reps : rep list -> (int * int) list
  val type_schema_of_rep : hol_type -> rep -> hol_type list
  val type_schema_of_reps :
    hol_type list -> rep list -> hol_type list
  val all_combinations_for_rep : rep -> int list list
end

structure Refute_ModelFinder_Rep :> REFUTE_MODEL_FINDER_REP = struct
  type polarity = Refute_ModelFinder_Util.polarity
  type hol_type = Type.hol_type
  type scope = Refute_ModelFinder_Scope.scope
  type offset_table = Refute_ModelFinder_Scope.offset_table

  structure Util = Refute_ModelFinder_Util
  structure MFH = Refute_ModelFinder_HOL
  structure MFS = Refute_ModelFinder_Scope

  datatype rep =
    Any
  | Formula of polarity
  | Atom of int * int
  | Struct of rep list
  | Vect of int * rep
  | Func of rep * rep
  | Opt of rep

  exception REP of string * rep list

  fun string_for_polarity Util.Pos = "+"
    | string_for_polarity Util.Neg = "-"
    | string_for_polarity Util.Neut = "="

  fun atomic_string_for_rep representation =
    let val string = string_for_rep representation
    in
      if String.isPrefix "[" string orelse
         not (Util.is_substring_of " " string) then
        string
      else
        "(" ^ string ^ ")"
    end
  and string_for_rep Any = "X"
    | string_for_rep (Formula polarity) =
        "F" ^ string_for_polarity polarity
    | string_for_rep (Atom (cardinality, offset)) =
        "A" ^ Int.toString cardinality ^
        (if offset = 0 then "" else "@" ^ Int.toString offset)
    | string_for_rep (Struct representations) =
        "[" ^ String.concatWith ", "
          (map string_for_rep representations) ^ "]"
    | string_for_rep (Vect (cardinality, representation)) =
        Int.toString cardinality ^ " x " ^
        atomic_string_for_rep representation
    | string_for_rep (Func (domain, range)) =
        atomic_string_for_rep domain ^ " => " ^
        string_for_rep range
    | string_for_rep (Opt representation) =
        atomic_string_for_rep representation ^ "?"

  fun is_Func (Func _) = true
    | is_Func _ = false

  fun is_Opt (Opt _) = true
    | is_Opt _ = false

  fun is_opt_rep (Func (_, range)) = is_opt_rep range
    | is_opt_rep (Opt _) = true
    | is_opt_rep _ = false

  fun safe_product location first second =
    first * second
    handle Overflow =>
      raise Util.TOO_LARGE (location, "result does not fit in int")

  fun safe_sum location first second =
    first + second
    handle Overflow =>
      raise Util.TOO_LARGE (location, "result does not fit in int")

  fun card_of_rep Any =
        raise REP ("Refute_ModelFinder_Rep.card_of_rep", [Any])
    | card_of_rep (Formula _) = 2
    | card_of_rep (Atom (cardinality, _)) = cardinality
    | card_of_rep (Struct representations) =
        List.foldl (fn (representation, result) =>
          safe_product "Refute_ModelFinder_Rep.card_of_rep" result
            (card_of_rep representation)) 1 representations
    | card_of_rep (Vect (cardinality, representation)) =
        Util.reasonable_power (card_of_rep representation) cardinality
    | card_of_rep (Func (domain, range)) =
        Util.reasonable_power (card_of_rep range) (card_of_rep domain)
    | card_of_rep (Opt representation) = card_of_rep representation

  fun arity_of_rep Any =
        raise REP ("Refute_ModelFinder_Rep.arity_of_rep", [Any])
    | arity_of_rep (Formula _) = 0
    | arity_of_rep (Atom _) = 1
    | arity_of_rep (Struct representations) =
        List.foldl (fn (representation, result) =>
          safe_sum "Refute_ModelFinder_Rep.arity_of_rep" result
            (arity_of_rep representation)) 0 representations
    | arity_of_rep (Vect (cardinality, representation)) =
        safe_product "Refute_ModelFinder_Rep.arity_of_rep" cardinality
          (arity_of_rep representation)
    | arity_of_rep (Func (domain, range)) =
        safe_sum "Refute_ModelFinder_Rep.arity_of_rep" (arity_of_rep domain)
          (arity_of_rep range)
    | arity_of_rep (Opt representation) =
        arity_of_rep representation

  fun min_univ_card_of_rep Any =
        raise REP
          ("Refute_ModelFinder_Rep.min_univ_card_of_rep", [Any])
    | min_univ_card_of_rep (Formula _) = 0
    | min_univ_card_of_rep (Atom (cardinality, offset)) =
        cardinality + offset
    | min_univ_card_of_rep (Struct representations) =
        List.foldl Int.max 0
          (map min_univ_card_of_rep representations)
    | min_univ_card_of_rep (Vect (_, representation)) =
        min_univ_card_of_rep representation
    | min_univ_card_of_rep (Func (domain, range)) =
        Int.max (min_univ_card_of_rep domain,
          min_univ_card_of_rep range)
    | min_univ_card_of_rep (Opt representation) =
        min_univ_card_of_rep representation

  fun is_one_rep (Atom _) = true
    | is_one_rep (Struct _) = true
    | is_one_rep (Vect _) = true
    | is_one_rep _ = false

  fun is_lone_rep (Opt representation) = is_one_rep representation
    | is_lone_rep representation = is_one_rep representation

  fun dest_Func (Func pair) = pair
    | dest_Func representation =
        raise REP ("Refute_ModelFinder_Rep.dest_Func",
          [representation])

  fun lazy_range_rep _ _ _ (Vect (_, representation)) =
        representation
    | lazy_range_rep _ _ _ (Func (_, range)) = range
    | lazy_range_rep offsets ty range_card (Opt representation) =
        Opt (lazy_range_rep offsets ty range_card representation)
    | lazy_range_rep offsets ty range_card
        (representation as Atom (cardinality, _)) =
        (case Lib.total Type.dom_rng ty of
             SOME (_, range_ty) =>
               Atom (if cardinality = 1 then 1 else range_card (),
                 MFS.offset_of_type offsets range_ty)
           | NONE => raise REP
               ("Refute_ModelFinder_Rep.lazy_range_rep",
                [representation]))
    | lazy_range_rep _ _ _ representation =
        raise REP ("Refute_ModelFinder_Rep.lazy_range_rep",
          [representation])

  fun binder_reps (Func (domain, range)) =
        domain :: binder_reps range
    | binder_reps _ = []

  fun body_rep (Func (_, range)) = body_rep range
    | body_rep representation = representation

  fun flip_rep_polarity (Formula polarity) =
        Formula (Util.flip_polarity polarity)
    | flip_rep_polarity (Func (domain, range)) =
        Func (domain, flip_rep_polarity range)
    | flip_rep_polarity representation = representation

  fun one_rep _ _ Any =
        raise REP ("Refute_ModelFinder_Rep.one_rep", [Any])
    | one_rep _ _ (Atom pair) = Atom pair
    | one_rep _ _ (Struct representations) =
        Struct representations
    | one_rep _ _ (Vect pair) = Vect pair
    | one_rep offsets ty (Opt representation) =
        one_rep offsets ty representation
    | one_rep offsets ty representation =
        Atom (card_of_rep representation,
          MFS.offset_of_type offsets ty)

  fun optable_rep offsets ty representation =
    case (Lib.total Type.dom_rng ty, representation) of
        (SOME (_, range_ty), Func (domain, range)) =>
          Func (domain, optable_rep offsets range_ty range)
      | _ => one_rep offsets ty representation

  fun opt_rep offsets ty representation =
    case (Lib.total Type.dom_rng ty, representation) of
        (SOME (_, range_ty), Func (domain, range)) =>
          Func (domain, opt_rep offsets range_ty range)
      | _ => Opt (optable_rep offsets ty representation)

  fun unopt_rep (Func (domain, range)) =
        Func (domain, unopt_rep range)
    | unopt_rep (Opt representation) = representation
    | unopt_rep representation = representation

  fun min_polarity left right =
    if left = right then
      left
    else if left = Util.Neut then
      right
    else if right = Util.Neut then
      left
    else
      raise Util.ARG
        ("Refute_ModelFinder_Rep.min_polarity",
         String.concatWith ", "
           (map (fn polarity =>
              "\"" ^ string_for_polarity polarity ^ "\"")
             [left, right]))

  (* Func must precede Vect: converting a Func with an Opt range to a
     Vect would lose partiality information. *)
  fun min_rep (Opt left) (Opt right) =
        Opt (min_rep left right)
    | min_rep (Opt representation) _ = Opt representation
    | min_rep _ (Opt representation) = Opt representation
    | min_rep (Formula left) (Formula right) =
        Formula (min_polarity left right)
    | min_rep (Formula polarity) _ = Formula polarity
    | min_rep _ (Formula polarity) = Formula polarity
    | min_rep (Atom pair) _ = Atom pair
    | min_rep _ (Atom pair) = Atom pair
    | min_rep (Struct left) (Struct right) =
        Struct (min_reps left right)
    | min_rep (Struct representations) _ =
        Struct representations
    | min_rep _ (Struct representations) =
        Struct representations
    | min_rep (left as Func (left_domain, left_range))
        (right as Func (right_domain, right_range)) =
        (case (is_opt_rep left_range, is_opt_rep right_range) of
             (true, false) => left
           | (false, true) => right
           | _ =>
               if left_domain = right_domain then
                 Func (left_domain, min_rep left_range right_range)
               else if min_rep left_domain right_domain = left_domain then
                 left
               else
                 right)
    | min_rep (Func pair) _ = Func pair
    | min_rep _ (Func pair) = Func pair
    | min_rep (Vect (left_card, left))
        (Vect (right_card, right)) =
        if left_card < right_card then
          Vect (left_card, left)
        else if left_card > right_card then
          Vect (right_card, right)
        else
          Vect (left_card, min_rep left right)
    | min_rep left right =
        raise REP ("Refute_ModelFinder_Rep.min_rep", [left, right])
  and min_reps [] _ = []
    | min_reps _ [] = []
    | min_reps (left :: lefts) (right :: rights) =
        if left = right then
          left :: min_reps lefts rights
        else if min_rep left right = left then
          left :: lefts
        else
          right :: rights

  fun card_of_domain_from_rep range_card representation =
    case representation of
        Atom (cardinality, _) => Util.exact_log range_card cardinality
      | Vect (cardinality, _) => cardinality
      | Func (domain, _) => card_of_rep domain
      | Opt inner => card_of_domain_from_rep range_card inner
      | _ => raise REP
          ("Refute_ModelFinder_Rep.card_of_domain_from_rep",
           [representation])

  fun rep_to_binary_rel_rep offsets ty representation =
    let
      fun domain (Func (domain_rep, range_rep)) =
            SOME (card_of_rep domain_rep, range_rep)
        | domain (Vect (cardinality, range_rep)) =
            SOME (cardinality, range_rep)
        | domain (Opt inner) = domain inner
        | domain _ = NONE

      fun aggregate_card rep =
        Util.exact_root 2 (card_of_domain_from_rep 2 rep)

      val (first_ty, second_ty, cardinality, paired_domain) =
        case Type.dom_rng ty of
            (first_ty, rest_ty) =>
              (case Lib.total Type.dom_rng rest_ty of
                   SOME (second_ty, _) =>
                     let
                       val card =
                         case domain representation of
                             SOME (first_card, after_first) =>
                               (case domain after_first of
                                    SOME (second_card, _) =>
                                      if first_card = second_card then
                                        first_card
                                      else
                                        raise REP
                                          ("Refute_ModelFinder_Rep." ^
                                           "rep_to_binary_rel_rep",
                                           [representation])
                                  | NONE => aggregate_card representation)
                           | NONE => aggregate_card representation
                     in
                       (first_ty, second_ty, card, false)
                     end
                 | NONE =>
                     if MFH.is_pair_type first_ty then
                       let
                         val (left_ty, right_ty) =
                           pairSyntax.dest_prod first_ty
                         val card = aggregate_card representation
                       in
                         (left_ty, right_ty, card, true)
                       end
                     else
                       raise REP
                         ("Refute_ModelFinder_Rep.rep_to_binary_rel_rep",
                          [representation]))
      val first = Atom (cardinality,
        MFS.offset_of_type offsets first_ty)
      val second = Atom (cardinality,
        MFS.offset_of_type offsets second_ty)
    in
      if paired_domain then
        Func (Struct [first, second], Formula Util.Neut)
      else
        (* HOL4 relationTheory relations are curried, unlike Isabelle's
           sets of pairs; preserve those application boundaries. *)
        Func (first, Func (second, Formula Util.Neut))
    end

  fun best_one_rep_for_type
        (scope as {card_assigns, ofs, ...} : scope) ty =
    case Lib.total Type.dom_rng ty of
        SOME (domain_ty, range_ty) =>
          Vect (MFH.card_of_type card_assigns domain_ty,
            best_one_rep_for_type scope range_ty)
      | NONE =>
          if MFH.is_pair_type ty then
            let val (left_ty, right_ty) = pairSyntax.dest_prod ty
            in
              Struct (map (best_one_rep_for_type scope)
                [left_ty, right_ty])
            end
          else
            Atom (MFH.card_of_type card_assigns ty,
              MFS.offset_of_type ofs ty)

  fun best_opt_set_rep_for_type
        (scope as {ofs, ...} : scope) ty =
    case Lib.total Type.dom_rng ty of
        SOME (domain_ty, range_ty) =>
          Func (best_one_rep_for_type scope domain_ty,
            best_opt_set_rep_for_type scope range_ty)
      | NONE =>
          opt_rep ofs ty (best_one_rep_for_type scope ty)

  fun best_non_opt_set_rep_for_type scope ty =
    case Lib.total Type.dom_rng ty of
        SOME (domain_ty, range_ty) =>
          let
            val domain = best_one_rep_for_type scope domain_ty
            val range = best_non_opt_set_rep_for_type scope range_ty
          in
            (* Cardinality two does not imply Boolean.
               In particular, a num range at card 2 must remain an Atom;
               only an actual Boolean range uses Formula. *)
            Func (domain,
              if MFH.is_boolean_type range_ty then Formula Util.Neut
              else range)
          end
      | NONE => best_one_rep_for_type scope ty

  fun best_set_rep_for_type
        (scope as {data_types, ...} : scope) ty =
    (if MFS.is_exact_type data_types true ty then
       best_non_opt_set_rep_for_type
     else
       best_opt_set_rep_for_type) scope ty

  fun atom_schema_of_rep Any =
        raise REP ("Refute_ModelFinder_Rep.atom_schema_of_rep", [Any])
    | atom_schema_of_rep (Formula _) = []
    | atom_schema_of_rep (Atom pair) = [pair]
    | atom_schema_of_rep (Struct representations) =
        atom_schema_of_reps representations
    | atom_schema_of_rep (Vect (cardinality, representation)) =
        Util.replicate_list cardinality
          (atom_schema_of_rep representation)
    | atom_schema_of_rep (Func (domain, range)) =
        atom_schema_of_rep domain @ atom_schema_of_rep range
    | atom_schema_of_rep (Opt representation) =
        atom_schema_of_rep representation
  and atom_schema_of_reps representations =
    List.concat (map atom_schema_of_rep representations)

  fun type_schema_of_rep _ (Formula _) = []
    | type_schema_of_rep ty (Atom _) = [ty]
    | type_schema_of_rep ty (Struct [left, right]) =
        if MFH.is_pair_type ty then
          let val (left_ty, right_ty) = pairSyntax.dest_prod ty
          in type_schema_of_reps [left_ty, right_ty] [left, right] end
        else
          raise REP ("Refute_ModelFinder_Rep.type_schema_of_rep",
            [Struct [left, right]])
    | type_schema_of_rep ty (Vect (cardinality, representation)) =
        (case Lib.total Type.dom_rng ty of
             SOME (_, range_ty) =>
               Util.replicate_list cardinality
                 (type_schema_of_rep range_ty representation)
           | NONE => raise REP
               ("Refute_ModelFinder_Rep.type_schema_of_rep",
                [Vect (cardinality, representation)]))
    | type_schema_of_rep ty (Func (domain, range)) =
        (case Lib.total Type.dom_rng ty of
             SOME (domain_ty, range_ty) =>
               type_schema_of_rep domain_ty domain @
               type_schema_of_rep range_ty range
           | NONE => raise REP
               ("Refute_ModelFinder_Rep.type_schema_of_rep",
                [Func (domain, range)]))
    | type_schema_of_rep ty (Opt representation) =
        type_schema_of_rep ty representation
    | type_schema_of_rep _ representation =
        raise REP ("Refute_ModelFinder_Rep.type_schema_of_rep",
          [representation])
  and type_schema_of_reps types representations =
    List.concat (ListPair.mapEq (fn (ty, representation) =>
      type_schema_of_rep ty representation) (types, representations))

  val all_combinations_for_rep =
    Util.all_combinations o atom_schema_of_rep
end
