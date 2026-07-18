(*  Title:      HolRefute/Refute_ModelFinder_Kodkod.sml
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009, 2010

Kodkod bounds and datatype axioms for the HOL4 Refute model finder.

This is part 1 of the port of Isabelle Nitpick's nitpick_kodkod.ML.
Formula translation is deliberately left to the following stage.
*)

signature REFUTE_MODEL_FINDER_KODKOD = sig
  type hol_type = Type.hol_type
  type nut = Refute_ModelFinder_Nut.nut
  type rep = Refute_ModelFinder_Rep.rep
  type data_type_spec = Refute_ModelFinder_Scope.data_type_spec
  type offset_table = Refute_ModelFinder_Scope.offset_table
  type kodkod_constrs = Refute_ModelFinder_Peephole.kodkod_constrs
  type need_values =
    (hol_type * (nut * int) list option) list

  val datatype_sym_break : int
  val kodkod_sym_break : int
  val sharing_level : int
  val flatten : bool
  val kodkod_settings : int -> Refute_Forl.setting list

  val univ_card :
    int -> int -> int -> Refute_Forl.bound list ->
    Refute_Forl.formula -> int
  val check_arity : string -> int -> int -> unit
  val empty_offset_table : unit -> offset_table
  val with_arity_retry :
    offset_table -> (offset_table -> 'a) -> 'a

  val kk_tuple : bool -> int -> int list -> Refute_Forl.tuple
  val tuple_set_from_atom_schema :
    (int * int) list -> Refute_Forl.tuple_set
  val sequential_int_bounds : int -> Refute_Forl.int_bound list
  val pow_of_two_int_bounds : int -> int -> Refute_Forl.int_bound list
  val bounds_and_axioms_for_built_in_rels_in_formulas :
    bool -> int -> int -> int -> int -> Refute_Forl.formula list ->
    Refute_Forl.bound list * Refute_Forl.formula list

  val bound_for_plain_rel : bool -> nut -> Refute_Forl.bound
  val bound_for_sel_rel :
    bool -> need_values -> data_type_spec list -> nut ->
    Refute_Forl.bound
  val merge_bounds : Refute_Forl.bound list -> Refute_Forl.bound list

  val empty_need_values : data_type_spec list -> need_values
  val declarative_axiom_for_plain_rel :
    kodkod_constrs -> nut -> Refute_Forl.formula
  val acyclicity_axioms_for_data_types :
    kodkod_constrs -> Refute_ModelFinder_Nut.nut
      Refute_ModelFinder_Nut.NameTable.table -> data_type_spec list ->
    Refute_Forl.formula list
  val sym_break_axioms_for_data_types :
    Refute_ModelFinder_HOL.mf_context -> int -> kodkod_constrs ->
    Refute_ModelFinder_Nut.nut Refute_ModelFinder_Nut.NameTable.table ->
    data_type_spec list -> Refute_Forl.formula list
  val declarative_axioms_for_data_types :
    Refute_ModelFinder_HOL.mf_context -> int -> int -> offset_table ->
    kodkod_constrs ->
    Refute_ModelFinder_Nut.nut Refute_ModelFinder_Nut.NameTable.table ->
    data_type_spec list -> Refute_Forl.formula list
end

structure Refute_ModelFinder_Kodkod
  :> REFUTE_MODEL_FINDER_KODKOD = struct

open Refute_Forl

structure MFH = Refute_ModelFinder_HOL
structure MFN = Refute_ModelFinder_Names
structure MFS = Refute_ModelFinder_Scope
structure MFP = Refute_ModelFinder_Peephole
structure MFR = Refute_ModelFinder_Rep
structure MFNT = Refute_ModelFinder_Nut
structure MFU = Refute_ModelFinder_Util

type hol_type = Type.hol_type
type nut = MFNT.nut
type rep = MFR.rep
type data_type_spec = MFS.data_type_spec
type offset_table = MFS.offset_table
type kodkod_constrs = MFP.kodkod_constrs
type need_values = (hol_type * (nut * int) list option) list

val datatype_sym_break = 5
val kodkod_sym_break = 15
val sharing_level = 3
val flatten = false

fun signed_int value =
  if value < 0 then "-" ^ Int.toString (~value) else Int.toString value

fun kodkod_settings delay =
  [("symmetry_breaking", Int.toString kodkod_sym_break),
   ("sharing", Int.toString sharing_level),
   ("flatten", Bool.toString flatten),
   ("delay", signed_int delay)]

fun same_type left right = Type.compare (left, right) = EQUAL
fun member equal value = List.exists (fn other => equal (value, other))
fun filter_out predicate = List.filter (not o predicate)
fun map_filter f = List.mapPartial f
fun maps f values = List.concat (map f values)
fun pull equal value values =
  value :: filter_out (fn other => equal (value, other)) values

fun single_atom atom = TupleSet [Tuple [atom]]

fun univ_card nat_card int_card main_j0 bounds formula =
  let
    fun rel_expr_func relation card =
      Int.max (card,
        case relation of
            Atom atom => atom + 1
          | AtomSeq (count, first) => first + count
          | _ => 0)
    fun tuple_func (Tuple atoms) card =
          List.foldl (fn (atom, result) => Int.max (atom + 1, result))
            card atoms
      | tuple_func _ card = card
    fun tuple_set_func tuple_set card =
      Int.max (card,
        case tuple_set of
            TupleAtomSeq (count, first) => first + count
          | _ => 0)
    val expr_funcs =
      {formula_func = fn _ => fn value => value,
       rel_expr_func = rel_expr_func,
       int_expr_func = fn _ => fn value => value}
    val tuple_funcs =
      {tuple_func = tuple_func, tuple_set_func = tuple_set_func}
    val bound_card = List.foldl (fn (bound, card) =>
      Refute_Forl.fold_bound expr_funcs tuple_funcs bound card) 1 bounds
    val formula_card = Refute_Forl.fold_formula expr_funcs formula bound_card
  in
    Int.max
      (main_j0 + List.foldl Int.max 2 [nat_card, int_card], formula_card)
  end

fun check_arity guilty universe_card arity =
  if arity > Refute_Forl.max_arity universe_card then
    raise MFU.TOO_LARGE
      ("Refute_ModelFinder_Kodkod.check_arity",
       "arity " ^ Int.toString arity ^
       (if guilty = "" then ""
        else " of Kodkod relation associated with \"" ^
          MFN.original_name guilty ^ "\"") ^
       " too large for a universe of size " ^
       Int.toString universe_card)
  else
    ()

fun empty_offset_table () =
  (* The second component is the HOL4 port's distinguished-default slot,
     replacing upstream's dummy-type key. *)
  (Redblackmap.mkDict Type.compare, 0)

fun offset_table_is_empty (table, _) = Redblackmap.numItems table = 0

fun with_arity_retry offsets build =
  build offsets
  handle error as (MFU.TOO_LARGE (location, _)) =>
    if location = "Refute_ModelFinder_Kodkod.check_arity" andalso
       not (offset_table_is_empty offsets) then
      build (empty_offset_table ())
    else
      raise error

fun kk_tuple debug universe_card atoms =
  if debug then
    Tuple atoms
  else
    TupleIndex (length atoms,
      List.foldl (fn (atom, result) =>
        result * universe_card + atom) 0 atoms)

(* Kodkodi infers the arity of an empty TupleProduct incorrectly.  Avoiding
   the product here is therefore required for correctness, not merely an
   optimization. *)
fun tuple_product (tuple_set as TupleSet []) _ = tuple_set
  | tuple_product _ (tuple_set as TupleSet []) = tuple_set
  | tuple_product left right = TupleProduct (left, right)

fun tuple_set_from_atom_schema [] = TupleSet []
  | tuple_set_from_atom_schema (first :: rest) =
      List.foldl (fn (schema, result) =>
        tuple_product result (TupleAtomSeq schema))
        (TupleAtomSeq first) rest

val upper_bound_for_rep =
  tuple_set_from_atom_schema o MFR.atom_schema_of_rep

fun sequential_int_bounds count =
  [(NONE, map single_atom (MFU.index_seq 0 count))]

fun pow_of_two_int_bounds bits first =
  let
    fun bounds 0 _ _ = []
      | bounds 1 power atom =
          [(SOME (~power), [single_atom atom])]
      | bounds remaining power atom =
          (SOME power, [single_atom atom]) ::
          bounds (remaining - 1) (2 * power) (atom + 1)
  in
    bounds (bits + 1) 1 first
  end

fun built_in_rels_in_formulas formulas =
  let
    fun rel_expr_func (Rel (index as (_, relation))) result =
          if relation < 0 andalso
             index <> MFP.unsigned_bit_word_sel_rel andalso
             index <> MFP.signed_bit_word_sel_rel andalso
             not (member (op =) index result) then
            index :: result
          else
            result
      | rel_expr_func _ result = result
    val funcs =
      {formula_func = fn _ => fn value => value,
       rel_expr_func = rel_expr_func,
       int_expr_func = fn _ => fn value => value}
  in
    List.foldl (fn (formula, result) =>
      Refute_Forl.fold_formula funcs formula result) [] formulas
  end

val max_table_size = 65536

fun check_table_size size =
  if size > max_table_size then
    raise MFU.TOO_LARGE
      ("Refute_ModelFinder_Kodkod.check_table_size",
       "precomputed table too large (" ^ Int.toString size ^ ")")
  else
    ()

fun tabulate_func1 debug universe_card (card, offset) f =
  let
    val _ = check_table_size card
    fun tuple atom =
      let val result = f atom
      in
        if result < 0 then NONE
        else SOME (kk_tuple debug universe_card
          [atom + offset, result + offset])
      end
  in
    map_filter tuple (MFU.index_seq 0 card)
  end

fun tabulate_op2 debug universe_card (card, offset) result_offset f =
  let
    val _ = check_table_size (card * card)
    fun tuple index =
      let
        val left = index div card
        val right = index - left * card
        val result = f (left, right)
      in
        if result < 0 then NONE
        else SOME (kk_tuple debug universe_card
          [left + offset, right + offset, result + result_offset])
      end
  in
    map_filter tuple (MFU.index_seq 0 (card * card))
  end

fun tabulate_op2_2 debug universe_card (card, offset) result_offset f =
  let
    val _ = check_table_size (card * card)
    fun tuple index =
      let
        val left = index div card
        val right = index - left * card
        val (result1, result2) = f (left, right)
      in
        if result1 < 0 orelse result2 < 0 then NONE
        else SOME (kk_tuple debug universe_card
          [left + offset, right + offset,
           result1 + result_offset, result2 + result_offset])
      end
  in
    map_filter tuple (MFU.index_seq 0 (card * card))
  end

fun tabulate_nat_op2 debug universe_card (card, offset) f =
  tabulate_op2 debug universe_card (card, offset) offset
    (MFP.atom_for_nat (card, 0) o f)

fun tabulate_int_op2 debug universe_card (card, offset) f =
  tabulate_op2 debug universe_card (card, offset) offset
    (MFP.atom_for_int (card, 0) o f o
     (fn (left, right) =>
       (MFP.int_for_atom (card, 0) left,
        MFP.int_for_atom (card, 0) right)))

fun tabulate_int_op2_2 debug universe_card (card, offset) f =
  tabulate_op2_2 debug universe_card (card, offset) offset
    ((fn (left, right) =>
       (MFP.atom_for_int (card, 0) left,
        MFP.atom_for_int (card, 0) right)) o f o
     (fn (left, right) =>
       (MFP.int_for_atom (card, 0) left,
        MFP.int_for_atom (card, 0) right)))

fun isa_div (left, right) =
  left div right handle General.Div => 0
fun isa_mod (left, right) =
  left mod right handle General.Div => left

fun isa_gcd (left, 0) = left
  | isa_gcd (left, right) = isa_gcd (right, isa_mod (left, right))

fun isa_lcm (left, right) =
  isa_div (left * right, isa_gcd (left, right))

val isa_zgcd = isa_gcd o (fn (left, right) => (abs left, abs right))

fun isa_norm_frac (left, right) =
  if right < 0 then isa_norm_frac (~left, ~right)
  else if left = 0 orelse right = 0 then (0, 1)
  else
    let val divisor = isa_zgcd (left, right)
    in (isa_div (left, divisor), isa_div (right, divisor)) end

fun tabulate_built_in_rel debug universe_card nat_card int_card main_j0
      (index as (arity, _)) =
  let
    val _ = check_arity "" universe_card arity
  in
    if index = MFP.not3_rel then
      ("not3", tabulate_func1 debug universe_card (2, main_j0)
        (fn value => 1 - value))
    else if index = MFP.suc_rel then
      ("suc", tabulate_func1 debug universe_card
        (universe_card - main_j0 - 1, main_j0) (fn value => value + 1))
    else if index = MFP.nat_add_rel then
      ("nat_add", tabulate_nat_op2 debug universe_card
        (nat_card, main_j0) (op +))
    else if index = MFP.int_add_rel then
      ("int_add", tabulate_int_op2 debug universe_card
        (int_card, main_j0) (op +))
    else if index = MFP.nat_subtract_rel then
      ("nat_subtract", tabulate_op2 debug universe_card
        (nat_card, main_j0) main_j0
        (fn (left, right) => MFU.nat_minus left right))
    else if index = MFP.int_subtract_rel then
      ("int_subtract", tabulate_int_op2 debug universe_card
        (int_card, main_j0) (op -))
    else if index = MFP.nat_multiply_rel then
      ("nat_multiply", tabulate_nat_op2 debug universe_card
        (nat_card, main_j0) (op *))
    else if index = MFP.int_multiply_rel then
      ("int_multiply", tabulate_int_op2 debug universe_card
        (int_card, main_j0) (op *))
    else if index = MFP.nat_divide_rel then
      ("nat_divide", tabulate_nat_op2 debug universe_card
        (nat_card, main_j0) isa_div)
    else if index = MFP.int_divide_rel then
      ("int_divide", tabulate_int_op2 debug universe_card
        (int_card, main_j0) isa_div)
    else if index = MFP.nat_less_rel then
      ("nat_less", tabulate_nat_op2 debug universe_card
        (nat_card, main_j0)
        (fn pair => MFU.int_from_bool (#1 pair < #2 pair)))
    else if index = MFP.int_less_rel then
      ("int_less", tabulate_int_op2 debug universe_card
        (int_card, main_j0)
        (fn pair => MFU.int_from_bool (#1 pair < #2 pair)))
    else if index = MFP.gcd_rel then
      ("gcd", tabulate_nat_op2 debug universe_card
        (nat_card, main_j0) isa_gcd)
    else if index = MFP.lcm_rel then
      ("lcm", tabulate_nat_op2 debug universe_card
        (nat_card, main_j0) isa_lcm)
    else if index = MFP.norm_frac_rel then
      ("norm_frac", tabulate_int_op2_2 debug universe_card
        (int_card, main_j0) isa_norm_frac)
    else
      raise MFU.ARG
        ("Refute_ModelFinder_Kodkod.tabulate_built_in_rel",
         "unknown relation")
  end

fun bound_for_built_in_rel debug universe_card nat_card int_card main_j0
      (index as (arity, relation)) =
  if arity = 2 andalso relation <= MFP.suc_rels_base then
    let
      val (sequence as (card, offset), tabulate) =
        MFP.atom_seq_for_suc_rel index
      val tuple_sets =
        if tabulate then
          [TupleSet (tabulate_func1 debug universe_card
            (card - 1, offset) (fn value => value + 1))]
        else
          [TupleSet [], tuple_set_from_atom_schema [sequence, sequence]]
    in
      ([(index, "suc")], tuple_sets)
    end
  else
    let
      val (nickname, tuples) = tabulate_built_in_rel debug universe_card
        nat_card int_card main_j0 index
    in
      ([(index, nickname)], [TupleSet tuples])
    end

fun axiom_for_built_in_rel (index as (arity, relation)) =
  if arity = 2 andalso relation <= MFP.suc_rels_base then
    let
      val (sequence as (card, offset), tabulate) =
        MFP.atom_seq_for_suc_rel index
    in
      if tabulate then NONE
      else if card < 2 then SOME (No (Rel index))
      else SOME (TotalOrdering
        (index, AtomSeq sequence, Atom offset, Atom (offset + 1)))
    end
  else
    NONE

fun bounds_and_axioms_for_built_in_rels_in_formulas debug universe_card
      nat_card int_card main_j0 formulas =
  let val relations = built_in_rels_in_formulas formulas
  in
    (map (bound_for_built_in_rel debug universe_card nat_card int_card
       main_j0) relations,
     map_filter axiom_for_built_in_rel relations)
  end

fun bound_comment debug nickname ty representation =
  MFN.original_name nickname ^
  (if debug then " :: " ^ Hol_pp.type_to_string ty else "") ^
  " : " ^ MFR.string_for_rep representation

fun bound_for_plain_rel debug
      (MFNT.FreeRel (index, ty, representation, nickname)) =
    ([(index, bound_comment debug nickname ty representation)],
     [TupleSet [], upper_bound_for_rep representation])
  | bound_for_plain_rel _ nut =
      raise MFNT.NUT
        ("Refute_ModelFinder_Kodkod.bound_for_plain_rel", [nut])

fun is_data_type_acyclic
      ({co = false, deep = true, ...} : data_type_spec) = true
  | is_data_type_acyclic _ = false

fun is_data_type_nat_like ({typ, constrs, ...} : data_type_spec) =
  case constrs of
      [first, second] =>
        let
          val argument_lists = map
            (MFH.constructor_arg_types o #const) [first, second]
        in
          (case argument_lists of
               [[], [argument]] => same_type argument typ
             | [[argument], []] => same_type argument typ
             | _ => false)
        end
    | _ => false

fun needed_values need_values ty =
  case List.find (fn (other, _) => same_type other ty) need_values of
      SOME (_, SOME values) => values
    | _ => []

fun all_values_are_needed need_values
      ({typ, card, ...} : data_type_spec) =
  length (needed_values need_values typ) = card

fun is_sel_of_constr index
      (MFNT.Construct (selectors, _, _, _), _) =
      List.exists (fn selector =>
        case selector of
            MFNT.FreeRel (other, _, _, _) => index = other
          | _ => false) selectors
  | is_sel_of_constr _ _ = false

fun find_constr_spec data_types constructor_name ty =
  let
    fun matches (spec : MFS.constr_spec) =
      MFH.constructor_name (#const spec) = constructor_name andalso
      same_type (MFH.constructor_result_type (#const spec)) ty
    fun search [] = NONE
      | search ((data_type : data_type_spec) :: rest) =
          (case List.find matches (#constrs data_type) of
               SOME spec => SOME spec
             | NONE => search rest)
  in
    case search data_types of
        SOME spec => spec
      | NONE => raise Feedback.mk_HOL_ERR
          "Refute_ModelFinder_Kodkod" "find_constr_spec"
          ("missing constructor specification for " ^ constructor_name)
  end

fun data_type_spec data_types ty =
  List.find (fn (spec : data_type_spec) => same_type (#typ spec) ty)
    data_types

fun tuple_union [] = TupleSet []
  | tuple_union (first :: rest) =
      List.foldl (fn (next, result) => TupleUnion (result, next))
        first rest

fun bound_for_sel_rel debug need_values data_types
      (nut as MFNT.FreeRel
        (index, ty, representation as MFR.Func
          (MFR.Atom (_, offset), range_rep), nickname)) =
    let
      val (domain_ty, range_ty) = Type.dom_rng ty
      val constructor_name = MFN.original_name nickname
      val {delta, epsilon, exclusive, explicit_max, ...} =
        find_constr_spec data_types constructor_name domain_ty
      val data_type = valOf (data_type_spec data_types domain_ty)
      val domain_need_values = needed_values need_values domain_ty
      val discriminator = range_rep = MFR.Formula MFU.Neut
      val complete_need_values =
        length domain_need_values = #card data_type
      val (my_need_values, other_need_values) =
        List.partition (is_sel_of_constr index) domain_need_values

      fun atom_seq_for_self_rec atom =
        if is_data_type_nat_like data_type then
          (1, atom + offset - 1)
        else
          (atom, offset)

      fun exact_bound_for_needy_atom atom =
        case List.filter (fn (_, other) => atom = other)
               my_need_values of
            [(MFNT.Construct (_, _, _, arguments), _)] =>
              let
                val selector = MFN.sel_no_from_name nickname
                val argument = List.nth (arguments, selector)
              in
                case List.find (fn (other, _) => other = argument)
                       (needed_values need_values range_ty) of
                    SOME (_, argument_atom) =>
                      SOME (TupleAtomSeq (1, argument_atom))
                  | NONE => NONE
              end
          | _ => NONE

      fun tuple_for_atom upper atom =
        let val owner = single_atom atom
        in
          if discriminator then owner
          else
            tuple_product owner
              (case exact_bound_for_needy_atom atom of
                   SOME exact => exact
                 | NONE =>
                     if upper then upper_bound_for_rep range_rep
                     else TupleSet [])
        end

      fun bound_tuples upper =
        if null domain_need_values then
          if upper then
            let val owners = TupleAtomSeq
              (epsilon - delta, delta + offset)
            in
              if discriminator then owners
              else tuple_product owners (upper_bound_for_rep range_rep)
            end
          else
            TupleSet []
        else
          let
            val atoms =
              if complete_need_values then map #2 my_need_values
              else
                MFU.index_seq (delta + offset) (epsilon - delta)
                |> filter_out (fn atom =>
                     List.exists (fn (_, other) => atom = other)
                       other_need_values)
          in
            tuple_union (map (tuple_for_atom upper) atoms)
          end

      val tuple_sets =
        if explicit_max = 0 orelse
           (complete_need_values andalso null my_need_values) then
          [TupleSet []]
        else if discriminator then
          if exclusive orelse
             all_values_are_needed need_values data_type then
            [bound_tuples true]
          else
            [TupleSet [], bound_tuples true]
        else
          let
            val upper =
              if same_type domain_ty range_ty andalso epsilon > delta andalso
                 is_data_type_acyclic data_type then
                tuple_union
                  (map (fn atom => tuple_product
                    (single_atom (atom + offset))
                    (TupleAtomSeq (atom_seq_for_self_rec atom)))
                    (MFU.index_seq delta (epsilon - delta)))
              else
                bound_tuples true
            val lower = bound_tuples false
          in
            if lower = upper then [lower] else [lower, upper]
          end
    in
      ([(index, bound_comment debug nickname ty representation)],
       tuple_sets)
    end
  | bound_for_sel_rel _ _ _ nut =
      raise MFNT.NUT
        ("Refute_ModelFinder_Kodkod.bound_for_sel_rel", [nut])

fun merge_bounds bounds =
  let
    fun arity (declarations, _) = #1 (#1 (hd declarations))
    fun add bound [] = [bound]
      | add bound (candidate :: rest) =
          if arity bound = arity candidate andalso
             #2 bound = #2 candidate then
            (#1 candidate @ #1 bound, #2 candidate) :: rest
          else
            candidate :: add bound rest
  in
    List.foldl (fn (bound, result) => add bound result) [] bounds
  end

fun unary_var_seq first count =
  map (fn index => Var (1, index)) (MFU.index_seq first count)

fun decls_for_atom_schema first schema =
  ListPair.mapEq (fn (index, atom_sequence) =>
    DeclOne ((1, index), AtomSeq atom_sequence))
    (MFU.index_seq first (length schema), schema)

fun d_n_ary_function
      ({kk_all, kk_join, kk_lone, kk_one, ...} : kodkod_constrs)
      representation relation =
  let val body_rep = MFR.body_rep representation
  in
    if MFR.is_lone_rep body_rep then
      let
        val binder_schema =
          MFR.atom_schema_of_reps (MFR.binder_reps representation)
        val body_schema = MFR.atom_schema_of_rep body_rep
        val one = MFR.is_one_rep body_rep
      in
        case relation of
            Rel index =>
              if length binder_schema = 1 andalso
                 length body_schema = 1 then
                (if one then Function else Functional)
                  (index, AtomSeq (hd binder_schema),
                   AtomSeq (hd body_schema))
              else
                let
                  val decls = decls_for_atom_schema (~1) binder_schema
                  val variables = unary_var_seq (~1)
                    (length binder_schema)
                  val joined = List.foldl
                    (fn (variable, result) => kk_join variable result)
                    relation variables
                in
                  kk_all decls ((if one then kk_one else kk_lone) joined)
                end
          | _ =>
              let
                val decls = decls_for_atom_schema (~1) binder_schema
                val variables = unary_var_seq (~1) (length binder_schema)
                val joined = List.foldl
                  (fn (variable, result) => kk_join variable result)
                  relation variables
              in
                kk_all decls ((if one then kk_one else kk_lone) joined)
              end
      end
    else
      True
  end

fun kk_n_ary_function kk representation (relation as Rel index) =
      if not (MFR.is_opt_rep representation) then
        if index = MFP.suc_rel then False
        else if index = MFP.nat_add_rel then
          MFP.formula_for_bool
            (MFR.card_of_rep (MFR.body_rep representation) = 1)
        else if index = MFP.nat_multiply_rel then
          MFP.formula_for_bool
            (MFR.card_of_rep (MFR.body_rep representation) <= 2)
        else
          d_n_ary_function kk representation relation
      else if index = MFP.nat_subtract_rel then
        True
      else
        d_n_ary_function kk representation relation
  | kk_n_ary_function kk representation relation =
      d_n_ary_function kk representation relation

fun kk_disjoint_sets _ [] = True
  | kk_disjoint_sets
      (kk as {kk_and, kk_no, kk_intersect, ...} : kodkod_constrs)
      (relation :: relations) =
    List.foldl (fn (other, result) =>
      kk_and (kk_no (kk_intersect relation other)) result)
      (kk_disjoint_sets kk relations) relations

fun declarative_axiom_for_plain_rel kk
      (MFNT.FreeRel
        (index, _, representation as MFR.Func _, nickname)) =
    let
      val effective_rep =
        if MFN.original_name nickname = "list$LIST_TO_SET" then
          MFR.unopt_rep representation
        else
          representation
    in
      kk_n_ary_function kk effective_rep (Rel index)
    end
  | declarative_axiom_for_plain_rel
      ({kk_lone, kk_one, ...} : kodkod_constrs)
      (MFNT.FreeRel (index, _, representation, _)) =
    if MFR.is_one_rep representation then kk_one (Rel index)
    else if MFR.is_lone_rep representation andalso
            MFR.card_of_rep representation > 1 then
      kk_lone (Rel index)
    else
      True
  | declarative_axiom_for_plain_rel _ nut =
      raise MFNT.NUT
        ("Refute_ModelFinder_Kodkod.declarative_axiom_for_plain_rel",
         [nut])

fun factor_types ty =
  if MFH.is_pair_type ty then
    let val (left, right) = pairSyntax.dest_prod ty
    in factor_types left @ factor_types right end
  else
    [ty]

fun generated_names_for_constructor constructor =
  let
    val data_ty = MFH.constructor_result_type constructor
    val constructor_name = MFH.constructor_name constructor
    val discriminator = MFNT.ConstName
      (#1 (Term.dest_var (MFN.mk_discriminator constructor_name
        (Type.-->(data_ty, Type.bool)))),
       Type.-->(data_ty, Type.bool), MFR.Any)
    val selector_types = List.concat
      (map factor_types (MFH.constructor_arg_types constructor))
    fun selector (index, range_ty) =
      let val term = MFN.mk_selector index constructor_name
        (Type.-->(data_ty, range_ty))
      in
        MFNT.ConstName
          (#1 (Term.dest_var term), Term.type_of term, MFR.Any)
      end
  in
    discriminator ::
    map selector (ListPair.zip
      (MFU.index_seq 0 (length selector_types), selector_types))
  end

fun const_triple relation_table name =
  case MFNT.the_name relation_table name of
      MFNT.FreeRel (index as (arity, _), _, representation, _) =>
        (Rel index, representation, arity)
    | nut => raise MFNT.NUT
        ("Refute_ModelFinder_Kodkod.const_triple", [nut])

fun discriminator_name constructor =
  hd (generated_names_for_constructor constructor)

fun discriminator_rel_expr relation_table constructor =
  #1 (const_triple relation_table (discriminator_name constructor))

fun selector_names constructor =
  tl (generated_names_for_constructor constructor)

type transition = (nut * rel_expr) * hol_type
type nfa = (hol_type * transition list) list

fun nfa_transitions_for_sel
      ({kk_project, ...} : kodkod_constrs) relation_table data_types name =
  let
    val ty = MFNT.type_of name
    val (relation, representation, arity) =
      const_triple relation_table name
    val type_schema = MFR.type_schema_of_rep ty representation
    val indexed = ListPair.zip
      (MFU.index_seq 1 (arity - 1), tl type_schema)
  in
    map_filter (fn (index, target_ty) =>
      if List.all (fn (spec : data_type_spec) =>
           not (same_type target_ty (#typ spec))) data_types then
        NONE
      else
        SOME ((name, kk_project relation [Num 0, Num index]), target_ty))
      indexed
  end

fun nfa_entry_for_data_type _ _ _
      ({co = true, ...} : data_type_spec) = NONE
  | nfa_entry_for_data_type _ _ _ {deep = false, ...} = NONE
  | nfa_entry_for_data_type kk relation_table data_types
      ({typ, constrs, ...} : data_type_spec) =
      SOME (typ, maps (fn spec =>
        maps (nfa_transitions_for_sel kk relation_table data_types)
          (selector_names (#const spec))) constrs)

val empty_binary_rel = Product (None, None)

fun direct_path_rel_exprs nfa start_ty final_ty =
  case List.find (fn (ty, _) => same_type ty final_ty) nfa of
      SOME (_, transitions) =>
        map (#2 o #1)
          (List.filter (fn (_, source_ty) => same_type source_ty start_ty)
            transitions)
    | NONE => []

fun fold_union ({kk_union, ...} : kodkod_constrs) relations initial =
  List.foldl (fn (relation, result) => kk_union result relation)
    initial relations

fun any_path_rel_expr kk nfa [] start_ty final_ty =
      fold_union kk (direct_path_rel_exprs nfa start_ty final_ty)
        (if same_type start_ty final_ty then Iden else empty_binary_rel)
  | any_path_rel_expr
      (kk as {kk_union, ...} : kodkod_constrs)
      nfa (ty :: tys) start_ty final_ty =
      kk_union (any_path_rel_expr kk nfa tys start_ty final_ty)
        (knot_path_rel_expr kk nfa tys start_ty ty final_ty)
and knot_path_rel_expr
      (kk as {kk_join, kk_reflexive_closure, ...} : kodkod_constrs)
      nfa tys start_ty knot_ty final_ty =
  kk_join
    (kk_join (any_path_rel_expr kk nfa tys knot_ty final_ty)
      (kk_reflexive_closure
        (loop_path_rel_expr kk nfa tys knot_ty)))
    (any_path_rel_expr kk nfa tys start_ty knot_ty)
and loop_path_rel_expr kk nfa [] start_ty =
      fold_union kk (direct_path_rel_exprs nfa start_ty start_ty)
        empty_binary_rel
  | loop_path_rel_expr
      (kk as {kk_union, kk_closure, ...} : kodkod_constrs)
      nfa (ty :: tys) start_ty =
      if same_type start_ty ty then
        kk_closure (loop_path_rel_expr kk nfa tys start_ty)
      else
        kk_union (loop_path_rel_expr kk nfa tys start_ty)
          (knot_path_rel_expr kk nfa tys start_ty ty start_ty)

structure TypeGraph = Graph(
  type key = hol_type
  val ord = Type.compare
  val pp = HOLPP.add_string o Hol_pp.type_to_string
)

fun strongly_connected_sub_nfas nfa =
  let
    fun add_transition source (_, target) graph =
      TypeGraph.add_edge (source, target)
        (TypeGraph.default_node (target, ())
          (TypeGraph.default_node (source, ()) graph))
    fun add_entry (source, transitions) graph =
      List.foldl (fn (transition, result) =>
        add_transition source transition result) graph transitions
    val graph = List.foldl (fn (entry, result) => add_entry entry result)
      TypeGraph.empty nfa
  in
    map (fn types => List.filter
      (fn (ty, _) => List.exists (same_type ty) types) nfa)
      (TypeGraph.strong_conn graph)
  end

fun nfas_for_data_types kk relation_table data_types =
  map_filter (nfa_entry_for_data_type kk relation_table data_types)
    data_types
  |> strongly_connected_sub_nfas

fun acyclicity_axioms_for_nfa _ [_] = []
  | acyclicity_axioms_for_nfa
      (kk as {kk_no, kk_intersect, ...} : kodkod_constrs) nfa =
      maps (fn (start_ty, _) =>
        [kk_no (kk_intersect
          (loop_path_rel_expr kk nfa
            (pull (fn (left, right) => same_type left right)
              start_ty (map #1 nfa)) start_ty)
          Iden)]) nfa

fun acyclicity_axioms_for_data_types kk relation_table data_types =
  maps (acyclicity_axioms_for_nfa kk)
    (nfas_for_data_types kk relation_table data_types)

fun all_ge
      ({kk_join, kk_reflexive_closure, ...} : kodkod_constrs)
      sequence relation =
  kk_join relation
    (kk_reflexive_closure
      (Rel (MFP.suc_rel_for_atom_seq sequence)))

fun gt ({kk_subset, kk_join, kk_closure, ...} : kodkod_constrs)
      sequence left right =
  kk_subset left
    (kk_join right (kk_closure
      (Rel (MFP.suc_rel_for_atom_seq sequence))))

(* [deviation] PLAN_M3 decision 29: Always tabulate the datatype successor
   order.  This makes the cycle-breaking bounds and symmetry-breaking order
   identical and avoids the upstream incompatible-orders spurious model. *)
fun should_tabulate_suc_for_type _ _ = true

fun lex_order_rel_expr
      (kk as {kk_implies, kk_and, kk_subset, kk_join, ...} : kodkod_constrs)
      data_types selector_triples =
  case selector_triples of
      [] => True
    | ((relation, MFR.Func (MFR.Atom _, MFR.Atom sequence), 2),
       (_, ty)) :: rest =>
        let
          val range_ty = #2 (Type.dom_rng ty)
          val order =
            (sequence, should_tabulate_suc_for_type data_types range_ty)
          val left = kk_join (Var (1, 1)) relation
          val right = kk_join (Var (1, 0)) relation
        in
          if null rest then
            gt kk order left right
          else
            kk_and (kk_subset left (all_ge kk order right))
              (kk_implies (kk_subset left right)
                (lex_order_rel_expr kk data_types rest))
        end
    | _ :: rest => lex_order_rel_expr kk data_types rest

fun is_nil_like_constr_type data_types constructor_ty =
  let val data_ty = #2 (boolSyntax.strip_fun constructor_ty)
  in
    case data_type_spec data_types data_ty of
        SOME {constrs, ...} =>
          (case List.filter (fn spec =>
                   not (MFS.is_self_recursive_constr_type
                     (Term.type_of (#const spec)))) constrs of
               [spec] => same_type (Term.type_of (#const spec)) constructor_ty
             | _ => false)
      | NONE => false
  end

fun compare_int (left, right) = Int.compare (left, right)

fun compare_constr_specs
      (left : MFS.constr_spec, right : MFS.constr_spec) =
  let
    fun continue EQUAL next = next ()
      | continue order _ = order
    val left_const = #const left
    val right_const = #const right
  in
    continue (compare_int (#delta left, #delta right)) (fn () =>
    continue (compare_int (#epsilon left, #epsilon right)) (fn () =>
    continue (compare_int
      (length (MFH.constructor_arg_types left_const),
       length (MFH.constructor_arg_types right_const))) (fn () =>
      String.compare (MFH.constructor_name left_const,
        MFH.constructor_name right_const))))
  end

fun sort_by compare values =
  Lib.sort (fn left => fn right => compare (left, right) <> GREATER) values

fun compare_data_types
      (left : data_type_spec, right : data_type_spec) =
  let
    fun bool_int value = if value then 1 else 0
    fun continue EQUAL next = next ()
      | continue order _ = order
  in
    continue (Int.compare (#card left, #card right)) (fn () =>
    continue (Int.compare
      (bool_int (#self_rec left), bool_int (#self_rec right))) (fn () =>
      Int.compare (length (#constrs left), length (#constrs right))))
  end

fun same_nut left right = MFNT.name_ord (left, right) = EQUAL

fun sym_break_axioms_for_constr_pair context
      (kk as {kk_all, kk_or, kk_implies, kk_and, kk_some,
              kk_intersect, kk_join, ...} : kodkod_constrs)
      relation_table nfas data_types
      (constructor_order, (first : MFS.constr_spec,
                           second : MFS.constr_spec)) =
  let
    val first_const = #const first
    val second_const = #const second
    val data_ty = MFH.constructor_result_type first_const
    val nfa =
      case List.find (fn component => List.exists
             (fn (ty, _) => same_type ty data_ty) component) nfas of
          SOME component => component
        | NONE => []
    val recursive_types = map #1 nfa

    fun rec_and_nonrec_selectors constructor =
      List.partition (fn selector =>
        let val range_ty = #2 (Type.dom_rng (MFNT.type_of selector))
        in List.exists (same_type range_ty) recursive_types end)
        (selector_names constructor)

    val (first_recursive, first_nonrecursive) =
      rec_and_nonrec_selectors first_const
    val first_selectors = first_recursive @ first_nonrecursive
  in
    if constructor_order = EQUAL andalso null first_selectors then
      []
    else
      let
        val discriminator_rep =
          #2 (const_triple relation_table
            (discriminator_name first_const))
        val sequence =
          case discriminator_rep of
              MFR.Func (MFR.Atom atom_sequence, MFR.Formula _) =>
                (atom_sequence,
                 should_tabulate_suc_for_type data_types data_ty)
            | representation => raise MFR.REP
                ("Refute_ModelFinder_Kodkod." ^
                 "sym_break_axioms_for_constr_pair",
                 [representation])
        val (second_recursive, second_nonrecursive) =
          rec_and_nonrec_selectors second_const
        val second_selectors = second_recursive @ second_nonrecursive

        fun selector_triples () =
          map (fn selector =>
            (const_triple relation_table selector,
             (selector, MFNT.type_of selector))) second_selectors

        fun filter_transitions no_direct selectors (source_ty, transitions) =
          (source_ty,
           List.filter (fn ((selector, _), target_ty) =>
             not ((constructor_order = EQUAL andalso
                   not (null selectors) andalso
                   same_nut selector (hd selectors)) orelse
                  (same_type target_ty data_ty andalso
                   (no_direct orelse
                    not (List.exists (same_nut selector) selectors)))))
             transitions)

        fun subterms no_direct selectors variable =
          loop_path_rel_expr kk
            (map (filter_transitions no_direct selectors) nfa)
            (filter_out (same_type data_ty) (map #1 nfa)) data_ty
          |> kk_join (Var (1, variable))

        val first_domain =
          discriminator_rel_expr relation_table first_const
        val second_domain =
          discriminator_rel_expr relation_table second_const
        val antecedent =
          if #delta second >= #epsilon first then True
          else if #delta first >= #epsilon second - 1 then False
          else gt kk sequence (Var (1, 1)) (Var (1, 0))
        val large_subterm =
          if is_nil_like_constr_type data_types
               (Term.type_of first_const) then
            True
          else
            kk_some (kk_intersect
              (subterms false second_selectors 1)
              (all_ge kk sequence (Var (1, 0))))
        val ordered_subterms =
          case constructor_order of
              EQUAL =>
                kk_and
                  (lex_order_rel_expr kk data_types
                    (selector_triples ()))
                  (kk_all [DeclOne ((1, 2),
                     subterms true first_selectors 0)]
                    (gt kk sequence (Var (1, 1)) (Var (1, 2))))
            | LESS =>
                kk_all [DeclOne ((1, 2),
                  subterms false first_selectors 0)]
                  (gt kk sequence (Var (1, 1)) (Var (1, 2)))
            | GREATER => False
      in
        [kk_all [DeclOne ((1, 0), first_domain),
                 DeclOne ((1, 1), second_domain)]
          (kk_implies antecedent
            (kk_or large_subterm ordered_subterms))]
      end
  end

fun sym_break_axioms_for_data_type context kk relation_table nfas
      data_types ({constrs, ...} : data_type_spec) =
  let
    val ordered = sort_by compare_constr_specs constrs
    fun all_pairs [] = []
      | all_pairs (first :: rest) =
          map (fn second => (first, second)) rest @ all_pairs rest
    val pairs = all_pairs ordered
    val entries =
      map (fn spec => (EQUAL, (spec, spec))) ordered @
      map (fn pair => (LESS, pair)) pairs @
      map (fn (left, right) => (GREATER, (right, left))) pairs
  in
    maps (sym_break_axioms_for_constr_pair context kk relation_table
      nfas data_types) entries
  end

val min_sym_break_card = 7

fun is_higher_order_type ty =
  MFH.is_fun_type ty orelse
  (case Lib.total Type.dest_thy_type ty of
       SOME {Args, ...} => List.exists is_higher_order_type Args
     | NONE => false)

fun first_order_constructor (spec : MFS.constr_spec) =
  List.all (not o is_higher_order_type)
    (MFH.constructor_arg_types (#const spec))

fun take count values =
  if count <= 0 orelse null values then []
  else hd values :: take (count - 1) (tl values)

fun sym_break_axioms_for_data_types context limit kk relation_table
      data_types =
  if limit = 0 then
    []
  else
    let
      val candidates = data_types
        |> List.filter is_data_type_acyclic
        |> List.filter (fn {card, constrs, ...} =>
             length constrs > 1 andalso card >= min_sym_break_card andalso
             List.all first_order_constructor constrs)
      val selected =
        if length candidates <= limit then candidates
        else take limit (rev (sort_by compare_data_types candidates))
      val nfas = nfas_for_data_types kk relation_table data_types
    in
      maps (sym_break_axioms_for_data_type context kk relation_table
        nfas data_types) selected
    end

fun sel_axioms_for_sel offset
      (kk as {kk_all, kk_formula_if, kk_subset, kk_no, kk_join, ...}
       : kodkod_constrs)
      need_values relation_table domain data_type
      ({const, delta, epsilon, exclusive, ...} : MFS.constr_spec)
      selector_number =
  let
    val selector = List.nth (selector_names const, selector_number)
    val (relation, representation, _) =
      const_triple relation_table selector
    val relation_index =
      case relation of
          Rel index => index
        | _ => raise MFU.BAD
            ("Refute_ModelFinder_Kodkod.sel_axioms_for_sel",
             "non-Rel")
    val range_rep = #2 (MFR.dest_Func representation)
    val sequence = (epsilon - delta, delta + offset)
  in
    if exclusive then
      [kk_n_ary_function kk
        (MFR.Func (MFR.Atom sequence, range_rep)) relation]
    else if all_values_are_needed need_values data_type then
      maps (fn (construct, atom) =>
        if is_sel_of_constr relation_index (construct, atom) then
          [kk_n_ary_function kk range_rep
            (kk_join (Atom atom) relation)]
        else []) (needed_values need_values (#typ data_type))
    else
      let val selected = kk_join (Var (1, 0)) relation
      in
        [kk_all [DeclOne ((1, 0), AtomSeq sequence)]
          (kk_formula_if (kk_subset (Var (1, 0)) domain)
            (kk_n_ary_function kk range_rep selected)
            (kk_no selected))]
      end
  end

fun sel_axioms_for_constr bits offset kk need_values relation_table
      (data_type : data_type_spec)
      (spec as {const, delta, epsilon, explicit_max, ...}
       : MFS.constr_spec) =
  let
    val honors_max =
      explicit_max < 0 orelse epsilon - delta <= explicit_max
  in
    if explicit_max = 0 then
      [MFP.formula_for_bool honors_max]
    else
      let
        val domain = discriminator_rel_expr relation_table const
        val max_axiom =
          if honors_max then True
          else if bits = 0 orelse
                  MFP.is_twos_complement_representable bits
                    (epsilon - delta) then
            LE (Cardinality domain, Num explicit_max)
          else
            raise MFU.TOO_SMALL
              ("Refute_ModelFinder_Kodkod.sel_axioms_for_constr",
               "bits value too small for max")
      in
        max_axiom ::
        maps (sel_axioms_for_sel offset kk need_values relation_table
          domain data_type spec)
          (MFU.index_seq 0 (length (selector_names const)))
      end
  end

fun uniqueness_axioms_for_constr
      ({kk_all, kk_implies, kk_and, kk_rel_eq, kk_lone, kk_join, ...}
       : kodkod_constrs)
      need_values relation_table (data_type : data_type_spec)
      ({const, ...} : MFS.constr_spec) =
  let
    val names = generated_names_for_constructor const
    val triples = map (const_triple relation_table) names
    val discriminator = #1 (hd triples)
    val selectors = tl triples
    fun same_selector_value (relation, _, _) =
      kk_rel_eq (kk_join (Var (1, 0)) relation)
        (kk_join (Var (1, 1)) relation)
  in
    if null selectors then
      [kk_lone discriminator]
    else if all_values_are_needed need_values data_type then
      []
    else
      [kk_all [DeclOne ((1, 0), discriminator),
               DeclOne ((1, 1), discriminator)]
        (kk_implies
          (MFU.fold1 kk_and (map same_selector_value selectors))
          (kk_rel_eq (Var (1, 0)) (Var (1, 1))))]
  end

fun partition_axioms_for_data_type offset
      (kk as {kk_rel_eq, kk_union, ...} : kodkod_constrs)
      need_values relation_table (data_type : data_type_spec) =
  let
    val constrs = #constrs data_type
    fun effective_max (spec : MFS.constr_spec) =
      #epsilon spec - #delta spec
  in
    if List.all #exclusive constrs then
      [MFP.formula_for_bool
        (List.foldl (fn (spec, result) => effective_max spec + result)
           0 constrs = #card data_type)]
    else if all_values_are_needed need_values data_type then
      []
    else
      let
        val relations = map (discriminator_rel_expr relation_table o #const)
          constrs
      in
        [kk_rel_eq (MFU.fold1 kk_union relations)
           (AtomSeq (#card data_type, offset)),
         kk_disjoint_sets kk relations]
      end
  end

fun other_axioms_for_data_type _ _ _ _ _
      ({deep = false, ...} : data_type_spec) = []
  | other_axioms_for_data_type bits offsets kk need_values relation_table
      (data_type : data_type_spec) =
      let
        val offset = MFS.offset_of_type offsets (#typ data_type)
      in
        maps (sel_axioms_for_constr bits offset kk need_values relation_table
          data_type) (#constrs data_type) @
        maps (uniqueness_axioms_for_constr kk need_values relation_table
          data_type) (#constrs data_type) @
        partition_axioms_for_data_type offset kk need_values relation_table
          data_type
      end

fun empty_need_values data_types =
  map (fn (spec : data_type_spec) => (#typ spec, SOME [])) data_types

fun declarative_axioms_for_data_types context sym_break bits offsets kk
      relation_table data_types =
  let
    (* PLAN_M3 decision 31: the need machinery remains in every bound and
       axiom helper, but M3 deliberately hard-wires need_us to []. *)
    val need_values = empty_need_values data_types
  in
    acyclicity_axioms_for_data_types kk relation_table data_types @
    sym_break_axioms_for_data_types context sym_break kk relation_table
      data_types @
    maps (other_axioms_for_data_type bits offsets kk need_values
      relation_table) data_types
  end

(* Upstream to_set_bool_op and kk_vect_set_bool_op are dead under the M3
   closure proof and are intentionally omitted (PLAN_M3 decision 31). *)

end
