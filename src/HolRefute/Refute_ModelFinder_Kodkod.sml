(*  Title:      HolRefute/Refute_ModelFinder_Kodkod.sml
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009, 2010

Kodkod translation, bounds, and datatype axioms for the HOL4 Refute model
finder.

This is a port of Isabelle Nitpick's nitpick_kodkod.ML.
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
  val kodkod_problem_settings :
    string list -> int -> int -> Refute_Forl.setting list

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
  val kodkod_formula_from_nut :
    offset_table -> kodkod_constrs -> nut -> Refute_Forl.formula

  type problem_metadata =
    {free_names : nut list,
     sel_names : nut list,
     nonsel_names : nut list,
     rel_table : nut Refute_ModelFinder_Nut.NameTable.table,
     unsound : bool,
     scope : Refute_ModelFinder_Scope.scope}
  type rich_problem = Refute_Forl.problem * problem_metadata
  type assembly_params =
    {debug : bool,
     peephole_optim : bool,
     total_consts : bool,
     datatype_sym_break : int,
     comment : string,
     settings : Refute_Forl.setting list,
     free_names : nut list,
     nonsel_names : nut list,
     nondef_us : nut list,
     def_us : nut list}
  val assemble_problem :
    assembly_params -> bool -> Refute_ModelFinder_Scope.scope -> rich_problem
  val assemble_problem_pair :
    assembly_params -> Refute_ModelFinder_Scope.scope ->
    rich_problem * rich_problem

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
structure KK = Refute_Forl

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

fun quote text = "\"" ^ text ^ "\""

fun kodkod_problem_settings solver bits delay =
  [("solver", String.concatWith ", " (map quote solver)),
   ("bit_width", Int.toString (if bits = 0 then 16 else bits + 1))] @
  kodkod_settings delay

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

fun singleton_from_combination atoms =
  MFU.fold1 (fn left => fn right => KK.Product (left, right))
    (map KK.Atom atoms)

fun all_singletons_for_rep representation =
  if MFR.is_lone_rep representation then
    map singleton_from_combination
      (MFR.all_combinations_for_rep representation)
  else
    raise MFR.REP
      ("Refute_ModelFinder_Kodkod.all_singletons_for_rep",
       [representation])

fun unpack_products (KK.Product (left, right)) =
      unpack_products left @ unpack_products right
  | unpack_products relation = [relation]

fun unpack_joins (KK.Join (left, right)) =
      unpack_joins left @ unpack_joins right
  | unpack_joins relation = [relation]

val empty_rel_for_rep = MFP.empty_n_ary_rel o MFR.arity_of_rep

fun full_rel_for_rep representation =
  case MFR.atom_schema_of_rep representation of
      [] => raise MFR.REP
        ("Refute_ModelFinder_Kodkod.full_rel_for_rep", [representation])
    | schema => MFU.fold1
        (fn left => fn right => KK.Product (left, right))
        (map KK.AtomSeq schema)

fun basic_rel_rel_let register
      ({kk_rel_let, ...} : kodkod_constrs) body relation =
  if MFP.inline_rel_expr relation then
    body relation
  else
    let val index = (KK.arity_of_rel_expr relation, register)
    in
      kk_rel_let [KK.AssignRelReg (index, relation)]
        (body (KK.RelReg index))
    end

val single_rel_rel_let = basic_rel_rel_let 0

fun double_rel_rel_let kk body first second =
  single_rel_rel_let kk
    (fn first' => basic_rel_rel_let 1 kk (body first') second) first

fun triple_rel_rel_let kk body first second third =
  double_rel_rel_let kk
    (fn first' => fn second' =>
      basic_rel_rel_let 2 kk (body first' second') third)
    first second

fun atom_from_formula
      ({kk_rel_if, ...} : kodkod_constrs) offset formula =
  kk_rel_if formula (KK.Atom (offset + 1)) (KK.Atom offset)

fun rel_expr_from_formula kk representation formula =
  case MFR.unopt_rep representation of
      MFR.Atom (2, offset) => atom_from_formula kk offset formula
    | _ => raise MFR.REP
        ("Refute_ModelFinder_Kodkod.rel_expr_from_formula",
         [representation])

fun unpack_vect_in_chunks
      ({kk_project_seq, ...} : kodkod_constrs) chunk_arity count relation =
  List.tabulate (count, fn index =>
    kk_project_seq relation (index * chunk_arity) chunk_arity)

fun kk_n_fold_join
      (kk as {kk_intersect, kk_product, kk_join, kk_project_seq, ...}
       : kodkod_constrs)
      one domain_rep result_rep argument relation =
  case MFR.arity_of_rep domain_rep of
      1 => kk_join argument relation
    | argument_arity =>
        let val unpacked = unpack_products argument
        in
          if one andalso length unpacked = argument_arity then
            List.foldl (fn (part, result) => kk_join part result)
              relation unpacked
          else if one andalso MFP.inline_rel_expr argument then
            List.foldl (fn (part, result) => kk_join part result)
              relation
              (unpack_vect_in_chunks kk 1 argument_arity argument)
          else
            kk_project_seq
              (kk_intersect
                (kk_product argument (full_rel_for_rep result_rep))
                relation)
              argument_arity (MFR.arity_of_rep result_rep)
        end

fun kk_case_switch
      (kk as {kk_union, kk_product, ...} : kodkod_constrs)
      old_rep new_rep relation old_values new_values =
  if old_values = new_values then
    relation
  else
    kk_n_fold_join kk true old_rep new_rep relation
      (MFU.fold1 kk_union
        (ListPair.mapEq (fn (left, right) => kk_product left right)
          (old_values, new_values)))

val lone_rep_fallback_max_card = 4096
val some_offset = 0

fun lone_rep_fallback kk new_rep old_rep relation =
  if old_rep = new_rep then
    relation
  else
    let val cardinality = MFR.card_of_rep old_rep
    in
      if MFR.is_lone_rep old_rep andalso MFR.is_lone_rep new_rep andalso
         cardinality = MFR.card_of_rep new_rep then
        if cardinality >= lone_rep_fallback_max_card then
          raise MFU.TOO_LARGE
            ("Refute_ModelFinder_Kodkod.lone_rep_fallback",
             "too high cardinality (" ^ Int.toString cardinality ^ ")")
        else
          kk_case_switch kk old_rep new_rep relation
            (all_singletons_for_rep old_rep)
            (all_singletons_for_rep new_rep)
      else
        raise MFR.REP
          ("Refute_ModelFinder_Kodkod.lone_rep_fallback",
           [old_rep, new_rep])
    end
and atom_from_rel_expr kk atom old_rep relation =
  case old_rep of
      MFR.Func (domain, range) =>
        let
          val domain_card = MFR.card_of_rep domain
          val range' =
            case range of
                MFR.Atom _ => range
              | _ => MFR.Atom (MFR.card_of_rep range, some_offset)
        in
          atom_from_rel_expr kk atom (MFR.Vect (domain_card, range'))
            (vect_from_rel_expr kk domain_card range' old_rep relation)
        end
    | MFR.Opt _ => raise MFR.REP
        ("Refute_ModelFinder_Kodkod.atom_from_rel_expr", [old_rep])
    | _ => lone_rep_fallback kk (MFR.Atom atom) old_rep relation
and struct_from_rel_expr kk reps old_rep relation =
  case old_rep of
      MFR.Atom _ =>
        lone_rep_fallback kk (MFR.Struct reps) old_rep relation
    | MFR.Struct old_reps =>
        if old_reps = reps then
          relation
        else if map MFR.card_of_rep old_reps =
                map MFR.card_of_rep reps then
          let
            val old_arities = map MFR.arity_of_rep old_reps
            val old_offsets = MFU.offset_list old_arities
            val old_relations = ListPair.mapEq
              (fn (offset, arity) =>
                #kk_project_seq kk relation offset arity)
              (old_offsets, old_arities)
          in
            MFU.fold1 (#kk_product kk)
              (ListPair.mapEq
                (fn (new_rep, (old_rep, old_relation)) =>
                  rel_expr_from_rel_expr kk new_rep old_rep old_relation)
                (reps, ListPair.zip (old_reps, old_relations)))
          end
        else
          lone_rep_fallback kk (MFR.Struct reps) old_rep relation
    | _ => raise MFR.REP
        ("Refute_ModelFinder_Kodkod.struct_from_rel_expr", [old_rep])
and vect_from_rel_expr kk count rep old_rep relation =
  case old_rep of
      MFR.Atom _ =>
        lone_rep_fallback kk (MFR.Vect (count, rep)) old_rep relation
    | MFR.Vect (old_count, old_body) =>
        if count = old_count andalso rep = old_body then relation
        else lone_rep_fallback kk (MFR.Vect (count, rep)) old_rep relation
    | MFR.Func (domain, MFR.Formula MFU.Neut) =>
        if count = MFR.card_of_rep domain then
          MFU.fold1 (#kk_product kk)
            (map (fn argument =>
              rel_expr_from_formula kk rep
                (#kk_subset kk argument relation))
              (all_singletons_for_rep domain))
        else
          raise MFR.REP
            ("Refute_ModelFinder_Kodkod.vect_from_rel_expr", [old_rep])
    | MFR.Func (domain, range) =>
        MFU.fold1 (#kk_product kk)
          (map (fn argument =>
            rel_expr_from_rel_expr kk rep range
              (kk_n_fold_join kk true domain range argument relation))
            (all_singletons_for_rep domain))
    | _ => raise MFR.REP
        ("Refute_ModelFinder_Kodkod.vect_from_rel_expr", [old_rep])
and func_from_no_opt_rel_expr kk domain range
      (MFR.Atom atom) relation =
    let
      val domain_card = MFR.card_of_rep domain
      val range' =
        case range of
            MFR.Atom _ => range
          | _ => MFR.Atom (MFR.card_of_rep range, some_offset)
    in
      func_from_no_opt_rel_expr kk domain range
        (MFR.Vect (domain_card, range'))
        (vect_from_rel_expr kk domain_card range'
          (MFR.Atom atom) relation)
    end
  | func_from_no_opt_rel_expr kk domain
      (MFR.Formula MFU.Neut) old_rep relation =
      (case old_rep of
           MFR.Vect (count, MFR.Atom (2, offset)) =>
             let
               val arguments = all_singletons_for_rep domain
               val values = unpack_vect_in_chunks kk 1 count relation
               fun entry argument value =
                 #kk_join kk value
                   (#kk_product kk (KK.Atom (offset + 1)) argument)
             in
               MFU.fold1 (#kk_union kk)
                 (ListPair.mapEq (fn (argument, value) =>
                    entry argument value) (arguments, values))
             end
         | MFR.Func (old_domain, MFR.Formula MFU.Neut) =>
             if domain = old_domain then
               relation
             else
               let
                 val schema = MFR.atom_schema_of_rep domain
                 val product = MFU.fold1 (#kk_product kk)
                   (unary_var_seq (~1) (length schema))
                 val converted = rel_expr_from_rel_expr kk old_domain
                   domain product
                 val equality =
                   if MFR.is_one_rep old_domain then #kk_subset kk
                   else #kk_rel_eq kk
               in
                 #kk_comprehension kk
                   (decls_for_atom_schema (~1) schema)
                   (equality converted relation)
               end
         | MFR.Func (old_domain, MFR.Atom (2, offset)) =>
             func_from_no_opt_rel_expr kk domain
               (MFR.Formula MFU.Neut)
               (MFR.Func (old_domain, MFR.Formula MFU.Neut))
               (#kk_join kk relation (KK.Atom (offset + 1)))
         | _ => raise MFR.REP
             ("Refute_ModelFinder_Kodkod.func_from_no_opt_rel_expr",
              [old_rep, MFR.Func (domain, MFR.Formula MFU.Neut)]))
  | func_from_no_opt_rel_expr kk domain range old_rep relation =
      (case old_rep of
           MFR.Vect (count, old_range) =>
             let
               val arguments = all_singletons_for_rep domain
               val values =
                 unpack_vect_in_chunks kk
                   (MFR.arity_of_rep old_range) count relation
                 |> map (rel_expr_from_rel_expr kk range old_range)
             in
               MFU.fold1 (#kk_union kk)
                 (ListPair.mapEq (fn (argument, value) =>
                    #kk_product kk argument value) (arguments, values))
             end
         | MFR.Func (old_domain, MFR.Formula MFU.Neut) =>
             (case range of
                  MFR.Atom (atom as (2, offset)) =>
                    let val schema = MFR.atom_schema_of_rep domain
                    in
                      if length schema = 1 then
                        #kk_override kk
                          (#kk_product kk (KK.AtomSeq (hd schema))
                            (KK.Atom offset))
                          (#kk_product kk relation
                            (KK.Atom (offset + 1)))
                      else
                        let
                          val domain_product =
                            MFU.fold1 (#kk_product kk)
                              (unary_var_seq (~1) (length schema))
                          val converted = rel_expr_from_rel_expr kk
                            old_domain domain domain_product
                          val range_var =
                            KK.Var (1, ~(length schema) - 1)
                          val range_atom = atom_from_formula kk offset
                            (#kk_subset kk converted relation)
                        in
                          #kk_comprehension kk
                            (decls_for_atom_schema (~1)
                              (schema @ [atom]))
                            (#kk_subset kk range_var range_atom)
                        end
                    end
                | _ => raise MFR.REP
                    ("Refute_ModelFinder_Kodkod." ^
                     "func_from_no_opt_rel_expr",
                     [old_rep, MFR.Func (domain, range)]))
         | MFR.Func (old_domain, old_range) =>
             if domain = old_domain andalso range = old_range then
               relation
             else
               let
                 val domain_schema = MFR.atom_schema_of_rep domain
                 val range_schema = MFR.atom_schema_of_rep range
                 val domain_product = MFU.fold1 (#kk_product kk)
                   (unary_var_seq (~1) (length domain_schema))
                 val converted_domain = rel_expr_from_rel_expr kk
                   old_domain domain domain_product
                 val range_product = MFU.fold1 (#kk_product kk)
                   (unary_var_seq (~(length domain_schema) - 1)
                     (length range_schema))
                 val converted_range = rel_expr_from_rel_expr kk
                   old_range range range_product
                 val application = kk_n_fold_join kk true old_domain
                   old_range converted_domain relation
                 val equality =
                   if MFR.is_one_rep old_range then #kk_subset kk
                   else #kk_rel_eq kk
               in
                 #kk_comprehension kk
                   (decls_for_atom_schema (~1)
                     (domain_schema @ range_schema))
                   (equality converted_range application)
               end
         | _ => raise MFR.REP
             ("Refute_ModelFinder_Kodkod.func_from_no_opt_rel_expr",
              [old_rep, MFR.Func (domain, range)]))
and rel_expr_from_rel_expr kk new_rep old_rep relation =
  let
    val old_unopt = MFR.unopt_rep old_rep
    val new_unopt = MFR.unopt_rep new_rep
  in
    if old_unopt <> old_rep andalso new_unopt = new_rep then
      raise MFR.REP
        ("Refute_ModelFinder_Kodkod.rel_expr_from_rel_expr",
         [old_rep, new_rep])
    else if new_unopt = old_unopt then
      relation
    else
      (case new_unopt of
           MFR.Atom atom => atom_from_rel_expr kk atom
         | MFR.Struct reps => struct_from_rel_expr kk reps
         | MFR.Vect (count, rep) => vect_from_rel_expr kk count rep
         | MFR.Func (domain, range) =>
             func_from_no_opt_rel_expr kk domain range
         | _ => raise MFR.REP
             ("Refute_ModelFinder_Kodkod.rel_expr_from_rel_expr",
              [old_rep, new_rep])) old_unopt relation
  end
and rel_expr_to_func kk domain range =
  rel_expr_from_rel_expr kk (MFR.Func (domain, range))

fun the_single [value] = value
  | the_single _ = raise MFU.ARG
      ("Refute_ModelFinder_Kodkod.the_single", "not a singleton")

fun flip_nums arity =
  map KK.Num (MFU.index_seq 1 arity @ [0])

fun binary_rel_types ty =
  let val (domain, range) = Type.dom_rng ty
  in
    if MFH.is_pair_type domain then
      pairSyntax.dest_prod domain
    else
      let val (second, _) = Type.dom_rng range
      in (domain, second) end
  end

fun dest_binary_rep representation =
  case MFR.unopt_rep representation of
      MFR.Func (MFR.Struct [first, second], body) =>
        (first, second, body, true)
    | MFR.Func (first, MFR.Func (second, body)) =>
        (first, second, body, false)
    | _ => raise MFR.REP
        ("Refute_ModelFinder_Kodkod.dest_binary_rep", [representation])

fun binary_rep paired first second body =
  if paired then MFR.Func (MFR.Struct [first, second], body)
  else MFR.Func (first, MFR.Func (second, body))

fun binary_rep_for_type ty first second body =
  binary_rep (MFH.is_pair_type (#1 (Type.dom_rng ty)))
    first second body

fun binary_domain_card representation =
  case Lib.total dest_binary_rep representation of
      SOME (first, second, _, _) =>
        MFR.card_of_rep first * MFR.card_of_rep second
    | NONE => MFR.card_of_domain_from_rep 2 representation

fun m4_translation location =
  raise MFU.NOT_SUPPORTED
    (location ^ ": unreachable in M3 by the closure proof in " ^
     "m3-kodkod-translation section 6 / PLAN_M3 section 9")

fun kodkod_formula_from_nut offsets
      (kk as {kk_all, kk_exist, kk_formula_let, kk_formula_if, kk_or,
              kk_not, kk_iff, kk_and, kk_subset, kk_rel_eq, kk_no,
              kk_lone, kk_some, kk_rel_let, kk_rel_if, kk_union,
              kk_difference, kk_intersect, kk_product, kk_join,
              kk_closure, kk_comprehension, kk_project,
              kk_project_seq, kk_not3, kk_nat_less, kk_int_less, ...}
       : kodkod_constrs) nut =
  let
    val main_offset = MFS.offset_of_type offsets Type.bool
    val bool_offset = main_offset
    val bool_atom_rep = MFR.Atom (2, main_offset)
    val false_atom = KK.Atom bool_offset
    val true_atom = KK.Atom (bool_offset + 1)

    fun formula_from_opt_atom polarity offset relation =
      case polarity of
          MFU.Neg => kk_not (kk_rel_eq relation (KK.Atom offset))
        | _ => kk_rel_eq relation (KK.Atom (offset + 1))

    val formula_from_atom = formula_from_opt_atom MFU.Pos

    fun unknown_formula polarity bad_nut =
      case polarity of
          MFU.Pos => KK.False
        | MFU.Neg => KK.True
        | MFU.Neut => raise MFNT.NUT
            ("Refute_ModelFinder_Kodkod.unknown_formula", [bad_nut])

    fun to_f candidate =
      case MFNT.rep_of candidate of
          MFR.Formula polarity =>
            (case candidate of
                 MFNT.Cst (MFNT.False, _, _) => KK.False
               | MFNT.Cst (MFNT.True, _, _) => KK.True
               | MFNT.Cst (MFNT.Unknown, _, _) =>
                   unknown_formula polarity candidate
               | MFNT.Cst (MFNT.Unrep, _, _) =>
                   unknown_formula polarity candidate
               | MFNT.Op1 (MFNT.Not, _, _, first) =>
                   kk_not (to_f_with_polarity
                     (MFU.flip_polarity polarity) first)
               | MFNT.Op1 (MFNT.Finite, _, _, first) =>
                   if MFR.is_opt_rep (MFNT.rep_of first) then
                     (* [deviation] PLAN_M3 decision 30: FINITE on an
                        optional set is the three-valued unknown Boolean,
                        never an affirmative fact in a sound problem. *)
                     unknown_formula polarity candidate
                   else
                     (case polarity of
                          MFU.Neut => KK.True
                        | MFU.Pos => KK.False
                        | MFU.Neg => KK.True)
               | MFNT.Op1 (MFNT.IsUnknown, _, _, first) =>
                   kk_no (to_r first)
               | MFNT.Op1 (MFNT.Cast, _, _, first) =>
                   to_f_with_polarity polarity first
               | MFNT.Op2 (MFNT.All, _, _, first, second) =>
                   kk_all (MFNT.untuple to_decl first)
                     (to_f_with_polarity polarity second)
               | MFNT.Op2 (MFNT.Exist, _, _, first, second) =>
                   kk_exist (MFNT.untuple to_decl first)
                     (to_f_with_polarity polarity second)
               | MFNT.Op2 (MFNT.Or, _, _, first, second) =>
                   kk_or (to_f_with_polarity polarity first)
                     (to_f_with_polarity polarity second)
               | MFNT.Op2 (MFNT.And, _, _, first, second) =>
                   kk_and (to_f_with_polarity polarity first)
                     (to_f_with_polarity polarity second)
               | MFNT.Op2 (MFNT.Less, ty, MFR.Formula inner_polarity,
                   first, second) =>
                   formula_from_opt_atom inner_polarity bool_offset
                     (to_r (MFNT.Op2 (MFNT.Less, ty,
                       MFR.Opt bool_atom_rep, first, second)))
               | MFNT.Op2 (MFNT.DefEq, _, _, first, second) =>
                   (case MFR.min_rep (MFNT.rep_of first)
                          (MFNT.rep_of second) of
                        MFR.Formula inner_polarity =>
                          kk_iff
                            (to_f_with_polarity inner_polarity first)
                            (to_f_with_polarity inner_polarity second)
                      | minimum_rep =>
                          let
                            fun arguments
                                  (MFNT.Op2 (MFNT.Apply, _, _, func,
                                     argument)) =
                                  argument :: arguments func
                              | arguments (MFNT.Tuple (_, _, items)) =
                                  items
                              | arguments _ = []
                            val optional_arguments =
                              List.filter
                                (MFR.is_opt_rep o MFNT.rep_of)
                                (arguments first)
                            val equality = kk_rel_eq
                              (to_rep minimum_rep first)
                              (to_rep minimum_rep second)
                          in
                            if null optional_arguments orelse
                               not (MFR.is_Opt minimum_rep) orelse
                               MFNT.is_eval_name first then
                              List.foldl (fn (argument, result) =>
                                kk_or (kk_no (to_r argument)) result)
                                equality optional_arguments
                            else
                              kk_subset (to_rep minimum_rep first)
                                (to_rep minimum_rep second)
                          end)
               | MFNT.Op2 (MFNT.Eq, _, _, first, second) =>
                   (case MFR.min_rep (MFNT.rep_of first)
                          (MFNT.rep_of second) of
                        MFR.Formula inner_polarity =>
                          kk_iff
                            (to_f_with_polarity inner_polarity first)
                            (to_f_with_polarity inner_polarity second)
                      | minimum_rep =>
                          if MFR.is_opt_rep minimum_rep then
                            if polarity = MFU.Neut then
                              kk_rel_eq (to_rep minimum_rep first)
                                (to_rep minimum_rep second)
                            else if MFNT.is_Cst MFNT.Unrep first then
                              to_could_be_unrep
                                (polarity = MFU.Neg) second
                            else if MFNT.is_Cst MFNT.Unrep second then
                              to_could_be_unrep
                                (polarity = MFU.Neg) first
                            else
                              let
                                val first_rel = to_rep minimum_rep first
                                val second_rel = to_rep minimum_rep second
                                val both_optional = List.all
                                  (MFR.is_opt_rep o MFNT.rep_of)
                                  [first, second]
                                fun optimized () =
                                  if polarity = MFU.Pos then
                                    if not both_optional then
                                      kk_rel_eq first_rel second_rel
                                    else if MFR.is_lone_rep minimum_rep
                                      andalso
                                      MFR.arity_of_rep minimum_rep = 1 then
                                      kk_some (kk_intersect first_rel
                                        second_rel)
                                    else
                                      raise MFU.SAME ()
                                  else if MFR.is_lone_rep minimum_rep then
                                    if MFR.arity_of_rep minimum_rep = 1 then
                                      kk_lone (kk_union first_rel
                                        second_rel)
                                    else if not both_optional then
                                      if MFR.is_opt_rep
                                           (MFNT.rep_of second) then
                                        kk_subset first_rel second_rel
                                      else
                                        kk_subset second_rel first_rel
                                    else
                                      raise MFU.SAME ()
                                  else
                                    raise MFU.SAME ()
                              in
                                optimized ()
                                handle MFU.SAME () =>
                                  formula_from_opt_atom polarity bool_offset
                                    (to_guard [first, second] bool_atom_rep
                                      (rel_expr_from_formula kk
                                        bool_atom_rep
                                        (kk_rel_eq first_rel second_rel)))
                              end
                          else
                            let
                              val first_rel = to_rep minimum_rep first
                              val second_rel = to_rep minimum_rep second
                            in
                              if MFR.is_one_rep minimum_rep then
                                let
                                  val first_parts =
                                    unpack_products first_rel
                                  val second_parts =
                                    unpack_products second_rel
                                in
                                  if length first_parts =
                                       length second_parts andalso
                                     map KK.arity_of_rel_expr first_parts =
                                       map KK.arity_of_rel_expr
                                         second_parts then
                                    MFU.fold1 kk_and
                                      (ListPair.mapEq
                                        (fn (first, second) =>
                                          kk_subset first second)
                                        (first_parts, second_parts))
                                  else
                                    kk_subset first_rel second_rel
                                end
                              else
                                kk_rel_eq first_rel second_rel
                            end)
               | MFNT.Op2 (MFNT.Apply, ty, _, first, second) =>
                   (case (polarity, MFNT.rep_of first) of
                        (MFU.Neg,
                         MFR.Func (domain, MFR.Formula MFU.Neut)) =>
                          kk_subset (to_opt domain second) (to_r first)
                      | _ => to_f_with_polarity polarity
                          (MFNT.Op2 (MFNT.Apply, ty,
                            MFR.Opt (MFR.Atom (2,
                              MFS.offset_of_type offsets ty)),
                            first, second)))
               | MFNT.Op3 (MFNT.Let, _, _, first, second, third) =>
                   kk_formula_let [to_expr_assign first second]
                     (to_f_with_polarity polarity third)
               | MFNT.Op3 (MFNT.If, _, _, first, second, third) =>
                   kk_formula_if (to_f first)
                     (to_f_with_polarity polarity second)
                     (to_f_with_polarity polarity third)
               | MFNT.FormulaReg (register, _, _) =>
                   KK.FormulaReg register
               | _ => raise MFNT.NUT
                   ("Refute_ModelFinder_Kodkod.to_f", [candidate]))
        | MFR.Atom (2, offset) =>
            formula_from_atom offset (to_r candidate)
        | _ => raise MFNT.NUT
            ("Refute_ModelFinder_Kodkod.to_f", [candidate])

    and to_f_with_polarity polarity candidate =
      case MFNT.rep_of candidate of
          MFR.Formula _ => to_f candidate
        | MFR.Atom (2, offset) =>
            formula_from_atom offset (to_r candidate)
        | MFR.Opt (MFR.Atom (2, offset)) =>
            formula_from_opt_atom polarity offset (to_r candidate)
        | _ => raise MFNT.NUT
            ("Refute_ModelFinder_Kodkod.to_f_with_polarity",
             [candidate])

    and to_r candidate =
      case candidate of
          MFNT.Cst (MFNT.False, _, MFR.Atom _) => false_atom
        | MFNT.Cst (MFNT.True, _, MFR.Atom _) => true_atom
        | MFNT.Cst (MFNT.Iden, _,
            MFR.Func (MFR.Struct [first_rep, second_rep],
              MFR.Formula MFU.Neut)) =>
            if first_rep = second_rep andalso
               MFR.arity_of_rep first_rep = 1 then
              kk_intersect KK.Iden
                (kk_product (full_rel_for_rep first_rep) KK.Univ)
            else
              let
                val first_schema = MFR.atom_schema_of_rep first_rep
                val second_schema = MFR.atom_schema_of_rep second_rep
                val first_arity = length first_schema
                val second_arity = length second_schema
                val first_rel = MFU.fold1 kk_product
                  (unary_var_seq 0 first_arity)
                val second_rel = MFU.fold1 kk_product
                  (unary_var_seq first_arity second_arity)
                val minimum_rep = MFR.min_rep first_rep second_rep
              in
                kk_comprehension
                  (decls_for_atom_schema 0
                    (first_schema @ second_schema))
                  (kk_rel_eq
                    (rel_expr_from_rel_expr kk minimum_rep first_rep
                      first_rel)
                    (rel_expr_from_rel_expr kk minimum_rep second_rep
                      second_rel))
              end
        | MFNT.Cst (MFNT.Iden, _,
            MFR.Func (MFR.Atom (1, offset), MFR.Formula MFU.Neut)) =>
            KK.Atom offset
        | MFNT.Cst (MFNT.Num value, ty, representation) =>
            if ty = MFH.int_type then
              (case MFP.atom_for_int
                 (MFR.card_of_rep representation,
                  MFS.offset_of_type offsets MFH.int_type) value of
                   ~1 => if MFR.is_opt_rep representation then KK.None
                         else raise MFNT.NUT
                           ("Refute_ModelFinder_Kodkod.to_r (Num)",
                            [candidate])
                 | atom => KK.Atom atom)
            else if ty = MFH.num_type then
              if value < MFR.card_of_rep representation then
                KK.Atom (value + MFS.offset_of_type offsets ty)
              else if MFR.is_opt_rep representation then
                KK.None
              else
                raise MFNT.NUT
                  ("Refute_ModelFinder_Kodkod.to_r (Num)", [candidate])
            else
              (* M4-only word numeral path; dead under the M3 closure
                 proof cited by PLAN_M3 section 9. *)
              m4_translation
                "Refute_ModelFinder_Kodkod.to_r (word Num)"
        | MFNT.Cst (MFNT.Unknown, _, representation) =>
            empty_rel_for_rep representation
        | MFNT.Cst (MFNT.Unrep, _, representation) =>
            empty_rel_for_rep representation
        | MFNT.Cst (MFNT.Suc, ty,
            MFR.Func (MFR.Atom sequence, _)) =>
            if #1 (Type.dom_rng ty) = MFH.num_type then
              kk_intersect (KK.Rel MFP.suc_rel)
                (kk_product KK.Univ (KK.AtomSeq sequence))
            else
              m4_translation
                "Refute_ModelFinder_Kodkod.to_r (word Suc)"
        | MFNT.Cst (MFNT.Add, ty, _) =>
            if #1 (Type.dom_rng ty) = MFH.num_type then
              KK.Rel MFP.nat_add_rel
            else if #1 (Type.dom_rng ty) = MFH.int_type then
              KK.Rel MFP.int_add_rel
            else
              m4_translation
                "Refute_ModelFinder_Kodkod.to_r (word Add)"
        | MFNT.Cst (MFNT.Subtract, ty, _) =>
            if #1 (Type.dom_rng ty) = MFH.num_type then
              KK.Rel MFP.nat_subtract_rel
            else if #1 (Type.dom_rng ty) = MFH.int_type then
              KK.Rel MFP.int_subtract_rel
            else
              m4_translation
                "Refute_ModelFinder_Kodkod.to_r (word Subtract)"
        | MFNT.Cst (MFNT.Multiply, ty, _) =>
            if #1 (Type.dom_rng ty) = MFH.num_type then
              KK.Rel MFP.nat_multiply_rel
            else if #1 (Type.dom_rng ty) = MFH.int_type then
              KK.Rel MFP.int_multiply_rel
            else
              m4_translation
                "Refute_ModelFinder_Kodkod.to_r (word Multiply)"
        | MFNT.Cst (MFNT.Divide, ty, _) =>
            if #1 (Type.dom_rng ty) = MFH.num_type then
              KK.Rel MFP.nat_divide_rel
            else if #1 (Type.dom_rng ty) = MFH.int_type then
              KK.Rel MFP.int_divide_rel
            else
              m4_translation
                "Refute_ModelFinder_Kodkod.to_r (word Divide)"
        | MFNT.Cst (MFNT.Gcd, _, _) =>
            (* M4-only rational support; unreachable by the M3 closure
               proof in m3-kodkod-translation section 6. *)
            m4_translation "Refute_ModelFinder_Kodkod.to_r (Gcd)"
        | MFNT.Cst (MFNT.Lcm, _, _) =>
            m4_translation "Refute_ModelFinder_Kodkod.to_r (Lcm)"
        | MFNT.Cst (MFNT.Fracs, _, _) =>
            m4_translation "Refute_ModelFinder_Kodkod.to_r (Fracs)"
        | MFNT.Cst (MFNT.NormFrac, _, _) =>
            m4_translation "Refute_ModelFinder_Kodkod.to_r (NormFrac)"
        | MFNT.Cst (MFNT.NatToInt, _,
            MFR.Func (MFR.Atom _, MFR.Atom _)) => KK.Iden
        | MFNT.Cst (MFNT.NatToInt, _,
            MFR.Func (MFR.Atom (_, nat_offset),
              MFR.Opt (MFR.Atom (int_card, int_offset)))) =>
            if nat_offset = int_offset then
              kk_intersect KK.Iden
                (kk_product
                  (KK.AtomSeq
                    (MFP.max_int_for_card int_card + 1, nat_offset))
                  KK.Univ)
            else
              raise MFU.BAD
                ("Refute_ModelFinder_Kodkod.to_r (NatToInt)",
                 "nat and int offsets differ")
        | MFNT.Cst (MFNT.IntToNat, _,
            MFR.Func (MFR.Atom (int_card, int_offset), nat_rep)) =>
            let
              val absolute_card = MFP.max_int_for_card int_card + 1
              val (nat_card, nat_offset) =
                the_single (MFR.atom_schema_of_rep nat_rep)
              val overlap = Int.min (nat_card, absolute_card)
            in
              if nat_offset = int_offset then
                kk_union
                  (kk_product
                    (KK.AtomSeq
                      (int_card - absolute_card,
                       int_offset + absolute_card))
                    (KK.Atom nat_offset))
                  (kk_intersect KK.Iden
                    (kk_product
                      (KK.AtomSeq (overlap, int_offset)) KK.Univ))
              else
                raise MFU.BAD
                  ("Refute_ModelFinder_Kodkod.to_r (IntToNat)",
                   "nat and int offsets differ")
            end
        | MFNT.Op1 (MFNT.Not, _, representation, first) =>
            kk_not3 (to_rep representation first)
        | MFNT.Op1 (MFNT.Finite, _, MFR.Opt (MFR.Atom _), _) =>
            (* [deviation] PLAN_M3 decision 30: the relational form of
               unknown FINITE is the empty optional Boolean atom. *)
            KK.None
        | MFNT.Op1 (MFNT.Converse, _, representation, first) =>
            let
              val (result_left, result_right, body_rep, paired) =
                dest_binary_rep representation
              val source_rep = binary_rep paired result_right result_left
                body_rep
              val target_rep = binary_rep paired result_left result_right
                body_rep
              val source_left_arity = MFR.arity_of_rep result_right
              val source_right_arity = MFR.arity_of_rep result_left
              val domain_arity = source_left_arity + source_right_arity
              val body_arity = MFR.arity_of_rep body_rep
              val columns = map KK.Num
                (MFU.index_seq source_left_arity source_right_arity @
                 MFU.index_seq 0 source_left_arity @
                 MFU.index_seq domain_arity body_arity)
            in
              rel_expr_from_rel_expr kk representation target_rep
                (kk_project (to_rep source_rep first) columns)
            end
        | MFNT.Op1 (MFNT.Closure, _, representation, first) =>
            if MFR.is_opt_rep representation then
              let
                val first_ty = MFNT.type_of first
                val binary_rep = MFR.rep_to_binary_rel_rep offsets
                  first_ty (MFR.unopt_rep (MFNT.rep_of first))
                val optional_binary_rep =
                  MFR.opt_rep offsets first_ty binary_rep
              in
                single_rel_rel_let kk
                  (fn relation =>
                    let
                      val true_relation =
                        kk_closure (kk_join relation true_atom)
                      val full_relation = full_rel_for_rep binary_rep
                      val false_relation = kk_difference full_relation
                        (kk_closure
                          (kk_difference full_relation
                            (kk_join relation false_atom)))
                    in
                      rel_expr_from_rel_expr kk representation
                        optional_binary_rep
                        (kk_union
                          (kk_product true_relation true_atom)
                          (kk_product false_relation false_atom))
                    end)
                  (to_rep optional_binary_rep first)
              end
            else
              let
                val binary_rep = MFR.rep_to_binary_rel_rep offsets
                  (MFNT.type_of first) (MFNT.rep_of first)
              in
                rel_expr_from_rel_expr kk representation binary_rep
                  (kk_closure (to_rep binary_rep first))
              end
        | MFNT.Op1 (MFNT.SingletonSet, _,
            MFR.Func (domain, MFR.Opt _),
            MFNT.Cst (MFNT.Unrep, _, _)) =>
            kk_product (full_rel_for_rep domain) false_atom
        | MFNT.Op1 (MFNT.SingletonSet, _, representation, first) =>
            (case representation of
                 MFR.Func (domain, MFR.Formula MFU.Neut) =>
                   to_rep domain first
               | MFR.Func (domain, MFR.Opt _) =>
                   single_rel_rel_let kk
                     (fn relation =>
                       kk_rel_if (kk_no relation)
                         (empty_rel_for_rep representation)
                         (rel_expr_to_func kk domain bool_atom_rep
                           (MFR.Func
                             (domain, MFR.Formula MFU.Neut)) relation))
                     (to_opt domain first)
               | _ => raise MFNT.NUT
                   ("Refute_ModelFinder_Kodkod.to_r (SingletonSet)",
                    [candidate]))
        | MFNT.Op1 (MFNT.SafeThe, _, representation, first) =>
            if MFR.is_opt_rep representation then
              kk_join
                (to_rep
                  (MFR.Func (MFR.unopt_rep representation,
                    MFR.Opt bool_atom_rep)) first)
                true_atom
            else
              to_rep
                (MFR.Func (representation, MFR.Formula MFU.Neut))
                first
        | MFNT.Op1 (MFNT.First, _, representation, first) =>
            to_nth_pair_sel 0 representation first
        | MFNT.Op1 (MFNT.Second, _, representation, first) =>
            to_nth_pair_sel 1 representation first
        | MFNT.Op1 (MFNT.Cast, _, representation, first) =>
            ((case MFNT.rep_of first of
                  MFR.Formula _ =>
                    (case MFR.unopt_rep representation of
                         MFR.Atom (2, offset) =>
                           atom_from_formula kk offset (to_f first)
                       | _ => raise MFU.SAME ())
                | _ => raise MFU.SAME ())
             handle MFU.SAME () =>
               rel_expr_from_rel_expr kk representation
                 (MFNT.rep_of first) (to_r first))
        | MFNT.Op2 (MFNT.All, ty, representation as MFR.Opt _,
            first, second) =>
            to_r (MFNT.Op1 (MFNT.Not, ty, representation,
              MFNT.Op2 (MFNT.Exist, ty, representation, first,
                MFNT.Op1 (MFNT.Not, ty, MFNT.rep_of second, second))))
        | MFNT.Op2 (MFNT.Exist, _, MFR.Opt _, first, second) =>
            let val declarations = MFNT.untuple to_decl first
            in
              if not (MFR.is_opt_rep (MFNT.rep_of second)) then
                kk_rel_if (kk_exist declarations (to_f second))
                  true_atom KK.None
              else
                let val relation = to_r second
                in
                  kk_union
                    (kk_rel_if
                      (kk_exist declarations
                        (kk_rel_eq relation true_atom))
                      true_atom KK.None)
                    (kk_rel_if
                      (kk_all declarations
                        (kk_rel_eq relation false_atom))
                      false_atom KK.None)
                end
            end
        | MFNT.Op2 (MFNT.Or, _, _, first, second) =>
            if MFR.is_opt_rep (MFNT.rep_of first) then
              kk_rel_if (to_f second) true_atom (to_r first)
            else
              kk_rel_if (to_f first) true_atom (to_r second)
        | MFNT.Op2 (MFNT.And, _, _, first, second) =>
            if MFR.is_opt_rep (MFNT.rep_of first) then
              kk_rel_if (to_f second) (to_r first) false_atom
            else
              kk_rel_if (to_f first) (to_r second) false_atom
        | MFNT.Op2 (MFNT.Less, _, _, first, second) =>
            if MFNT.type_of first = MFH.num_type then
              if MFNT.is_Cst MFNT.Unrep first then
                to_compare_with_unrep second false_atom
              else if MFNT.is_Cst MFNT.Unrep second then
                to_compare_with_unrep first true_atom
              else
                kk_nat_less (to_integer first) (to_integer second)
            else if MFNT.type_of first = MFH.int_type then
              kk_int_less (to_integer first) (to_integer second)
            else
              (* Word comparison is M4-only and dead by the M3 closure
                 proof in m3-kodkod-translation section 6. *)
              m4_translation
                "Refute_ModelFinder_Kodkod.to_r (word Less)"
        | MFNT.Op2 (MFNT.Triad, _, MFR.Opt (MFR.Atom (2, offset)),
            first, second) =>
            let
              val first_formula = to_f first
              val second_formula = to_f second
            in
              if first_formula = second_formula then
                atom_from_formula kk offset first_formula
              else
                kk_union
                  (kk_rel_if first_formula true_atom KK.None)
                  (kk_rel_if second_formula KK.None false_atom)
            end
        | MFNT.Op2 (MFNT.Composition, _, representation,
            first, second) =>
            let
              val (first_ty, middle_ty) =
                binary_rel_types (MFNT.type_of first)
              val (_, last_ty) =
                binary_rel_types (MFNT.type_of second)
              val first_middle_card =
                binary_domain_card (MFNT.rep_of first)
              val middle_last_card =
                binary_domain_card (MFNT.rep_of second)
              val first_last_card = binary_domain_card representation
              val first_card = MFU.exact_root 2
                (first_last_card * first_middle_card div
                 middle_last_card)
              val middle_card = MFU.exact_root 2
                (first_middle_card * middle_last_card div
                 first_last_card)
              val last_card = MFU.exact_root 2
                (middle_last_card * first_last_card div
                 first_middle_card)
              val first_rep = MFR.Atom (first_card,
                MFS.offset_of_type offsets first_ty)
              val middle_rep = MFR.Atom (middle_card,
                MFS.offset_of_type offsets middle_ty)
              val last_rep = MFR.Atom (last_card,
                MFS.offset_of_type offsets last_ty)
              val body_rep = MFR.body_rep representation
              val result =
                case body_rep of
                    MFR.Formula MFU.Neut =>
                      kk_join
                        (to_rep
                          (binary_rep_for_type (MFNT.type_of first)
                            first_rep middle_rep
                            (MFR.Formula MFU.Neut)) first)
                        (to_rep
                          (binary_rep_for_type (MFNT.type_of second)
                            middle_rep last_rep
                            (MFR.Formula MFU.Neut)) second)
                  | MFR.Opt (MFR.Atom (2, _)) =>
                      let
                        fun must left right item =
                          kk_join
                            (to_rep
                              (binary_rep_for_type (MFNT.type_of item)
                                left right body_rep) item)
                            true_atom
                        fun may left right item =
                          kk_difference
                            (full_rel_for_rep (MFR.Struct [left, right]))
                            (kk_join
                              (to_rep
                                (binary_rep_for_type (MFNT.type_of item)
                                  left right body_rep) item)
                              false_atom)
                      in
                        kk_union
                          (kk_product
                            (kk_join
                              (must first_rep middle_rep first)
                              (must middle_rep last_rep second))
                            true_atom)
                          (kk_product
                            (kk_difference
                              (full_rel_for_rep
                                (MFR.Struct [first_rep, last_rep]))
                              (kk_join
                                (may first_rep middle_rep first)
                                (may middle_rep last_rep second)))
                            false_atom)
                      end
                  | _ => raise MFNT.NUT
                      ("Refute_ModelFinder_Kodkod.to_r (Composition)",
                       [candidate])
              val result_rep = binary_rep_for_type
                (MFNT.type_of candidate) first_rep last_rep body_rep
            in
              rel_expr_from_rel_expr kk representation result_rep result
            end
        | MFNT.Op2 (MFNT.Apply, ty, representation,
            function as MFNT.Op2 (MFNT.Apply, _, _,
              MFNT.Cst (MFNT.Subtract, _, _), first), second) =>
            if ty <> MFH.num_type then
              to_apply representation function second
            else if MFNT.is_Cst MFNT.Unrep second andalso
                    not (MFR.is_opt_rep (MFNT.rep_of first)) then
              KK.Atom (MFS.offset_of_type offsets MFH.num_type)
            else
              List.foldl (fn (relation, result) =>
                kk_join relation result)
                (KK.Rel MFP.nat_subtract_rel)
                (map to_integer [first, second])
        | MFNT.Op2 (MFNT.Apply, _, representation, first, second) =>
            to_apply representation first second
        | MFNT.Op2 (MFNT.Lambda, _,
            representation as MFR.Opt (MFR.Atom (1, offset)),
            first, second) =>
            to_guard [first, second] representation (KK.Atom offset)
        | MFNT.Op2 (MFNT.Lambda, _,
            MFR.Func (_, MFR.Formula MFU.Neut), first, second) =>
            kk_comprehension (MFNT.untuple to_decl first) (to_f second)
        | MFNT.Op2 (MFNT.Lambda, _,
            MFR.Func (_, range), first, second) =>
            let
              val domain_decls = MFNT.untuple to_decl first
              val range_schema = MFR.atom_schema_of_rep range
              val range_decls =
                decls_for_atom_schema (~1) range_schema
              val range_vars =
                unary_var_seq (~1) (length range_decls)
            in
              kk_comprehension (domain_decls @ range_decls)
                (kk_subset (MFU.fold1 kk_product range_vars)
                  (to_rep range second))
            end
        | MFNT.Op3 (MFNT.Let, _, representation,
            first, second, third) =>
            kk_rel_let [to_expr_assign first second]
              (to_rep representation third)
        | MFNT.Op3 (MFNT.If, _, representation,
            first, second, third) =>
            if MFR.is_opt_rep (MFNT.rep_of first) then
              triple_rel_rel_let kk
                (fn first_rel => fn second_rel => fn third_rel =>
                  let val empty = empty_rel_for_rep representation
                  in
                    MFU.fold1 kk_union
                      [kk_rel_if
                         (kk_rel_eq first_rel true_atom)
                         second_rel empty,
                       kk_rel_if
                         (kk_rel_eq first_rel false_atom)
                         third_rel empty,
                       kk_rel_if
                         (kk_rel_eq second_rel third_rel)
                         (if MFP.inline_rel_expr second_rel then
                            second_rel
                          else third_rel)
                         empty]
                  end)
                (to_r first) (to_rep representation second)
                (to_rep representation third)
            else
              kk_rel_if (to_f first) (to_rep representation second)
                (to_rep representation third)
        | MFNT.Tuple (_, representation, items) =>
            (case MFR.unopt_rep representation of
                 MFR.Struct reps => to_product reps items
               | MFR.Vect (count, rep) =>
                   to_product (List.tabulate (count, fn _ => rep)) items
               | MFR.Atom (1, offset) =>
                   kk_rel_if
                     (kk_some (MFU.fold1 kk_product (map to_r items)))
                     (KK.Atom offset) KK.None
               | _ => raise MFNT.NUT
                   ("Refute_ModelFinder_Kodkod.to_r (Tuple)",
                    [candidate]))
        | MFNT.Construct ([only], _, _, []) => to_r only
        | MFNT.Construct (discriminator :: selectors, _, _, arguments) =>
            let
              fun inverse selector argument =
                let
                  val (domain, range) =
                    MFR.dest_Func (MFNT.rep_of selector)
                  val selector_rel = to_r selector
                  val argument_rel = to_opt range argument
                in
                  if MFR.is_one_rep range then
                    kk_n_fold_join kk true range domain argument_rel
                      (kk_project selector_rel
                        (flip_nums (MFR.arity_of_rep range)))
                  else
                    let
                      val relation = kk_comprehension
                        [KK.DeclOne ((1, ~1), to_r discriminator)]
                        (kk_rel_eq
                          (kk_join (KK.Var (1, ~1)) selector_rel)
                          argument_rel)
                    in
                      if MFR.is_opt_rep (MFNT.rep_of argument) then
                        to_guard [argument] domain relation
                      else
                        relation
                    end
                end
            in
              MFU.fold1 kk_intersect
                (ListPair.mapEq (fn (selector, argument) =>
                  inverse selector argument) (selectors, arguments))
            end
        | MFNT.BoundRel (index, _, _, _) => KK.Var index
        | MFNT.FreeRel (index, _, _, _) => KK.Rel index
        | MFNT.RelReg (register, _, representation) =>
            KK.RelReg (MFR.arity_of_rep representation, register)
        | _ => raise MFNT.NUT
            ("Refute_ModelFinder_Kodkod.to_r", [candidate])

    and to_decl (MFNT.BoundRel (index, _, representation, _)) =
          KK.DeclOne
            (index,
             KK.AtomSeq
               (the_single (MFR.atom_schema_of_rep representation)))
      | to_decl candidate = raise MFNT.NUT
          ("Refute_ModelFinder_Kodkod.to_decl", [candidate])

    and to_expr_assign (MFNT.FormulaReg (register, _, _)) value =
          KK.AssignFormulaReg (register, to_f value)
      | to_expr_assign
          (MFNT.RelReg (register, _, representation)) value =
          KK.AssignRelReg
            ((MFR.arity_of_rep representation, register), to_r value)
      | to_expr_assign target _ = raise MFNT.NUT
          ("Refute_ModelFinder_Kodkod.to_expr_assign", [target])

    and to_atom (atom as (_, offset)) candidate =
      case MFNT.rep_of candidate of
          MFR.Formula _ => atom_from_formula kk offset (to_f candidate)
        | representation => atom_from_rel_expr kk atom representation
            (to_r candidate)

    and to_struct reps candidate =
      struct_from_rel_expr kk reps (MFNT.rep_of candidate)
        (to_r candidate)

    and to_vect count rep candidate =
      vect_from_rel_expr kk count rep (MFNT.rep_of candidate)
        (to_r candidate)

    and to_func domain range candidate =
      rel_expr_to_func kk domain range (MFNT.rep_of candidate)
        (to_r candidate)

    and to_opt rep candidate =
      let val old_rep = MFNT.rep_of candidate
      in
        if MFR.is_opt_rep old_rep then
          rel_expr_from_rel_expr kk (MFR.Opt rep) old_rep
            (to_r candidate)
        else
          to_rep rep candidate
      end

    and to_rep (MFR.Atom atom) candidate = to_atom atom candidate
      | to_rep (MFR.Struct reps) candidate = to_struct reps candidate
      | to_rep (MFR.Vect (count, rep)) candidate =
          to_vect count rep candidate
      | to_rep (MFR.Func (domain, range)) candidate =
          to_func domain range candidate
      | to_rep (MFR.Opt rep) candidate = to_opt rep candidate
      | to_rep representation _ = raise MFR.REP
          ("Refute_ModelFinder_Kodkod.to_rep", [representation])

    and to_integer candidate =
      to_opt
        (MFR.one_rep offsets (MFNT.type_of candidate)
          (MFNT.rep_of candidate)) candidate

    and to_guard guards representation relation =
      let
        val unpacked = unpack_joins relation
        val plain_guards = guards
          |> List.filter (MFR.is_Opt o MFNT.rep_of)
          |> map to_r
          |> List.filter (fn guard => not (member (op =) guard unpacked))
        val function_guards = List.filter (fn guard =>
          MFR.is_Func (MFNT.rep_of guard) andalso
          MFR.is_opt_rep (MFNT.rep_of guard)) guards
        val function_relations = map to_r function_guards
        val guard_formulas = map kk_no plain_guards @
          ListPair.mapEq
            (fn (guard, guard_relation) =>
              kk_not (kk_n_ary_function kk
                (MFR.unopt_rep (MFNT.rep_of guard)) guard_relation))
            (function_guards, function_relations)
      in
        if null guard_formulas then
          relation
        else
          kk_rel_if (MFU.fold1 kk_or guard_formulas)
            (empty_rel_for_rep representation) relation
      end

    and to_project new_rep old_rep relation offset =
      rel_expr_from_rel_expr kk new_rep old_rep
        (kk_project_seq relation offset (MFR.arity_of_rep old_rep))

    and to_product reps items =
      MFU.fold1 kk_product
        (ListPair.mapEq (fn (rep, item) => to_opt rep item)
          (reps, items))

    and to_nth_pair_sel index result_rep candidate =
      case candidate of
          MFNT.Tuple (_, _, items) =>
            to_rep result_rep (List.nth (items, index))
        | _ =>
            let
              val representation = MFNT.rep_of candidate
              val (first_ty, second_ty) =
                pairSyntax.dest_prod (MFNT.type_of candidate)
              val reps =
                case MFR.unopt_rep representation of
                    MFR.Struct (pair as [_, _]) => pair
                  | _ =>
                      let
                        val result_card = MFR.card_of_rep result_rep
                        val other_card =
                          MFR.card_of_rep representation div result_card
                        val (first_card, second_card) =
                          if index = 0 then (result_card, other_card)
                          else (other_card, result_card)
                      in
                        [MFR.Atom (first_card,
                           MFS.offset_of_type offsets first_ty),
                         MFR.Atom (second_card,
                           MFS.offset_of_type offsets second_ty)]
                      end
              val selected_rep = List.nth (reps, index)
              val column =
                if index = 0 then 0
                else MFR.arity_of_rep (hd reps)
            in
              to_project result_rep selected_rep
                (to_rep (MFR.Opt (MFR.Struct reps)) candidate) column
            end

    and to_apply (representation as MFR.Formula _) _ _ =
          raise MFR.REP
            ("Refute_ModelFinder_Kodkod.to_apply", [representation])
      | to_apply result_rep function argument =
          (case MFR.unopt_rep (MFNT.rep_of function) of
               MFR.Atom (1, offset) =>
                 to_guard [argument] result_rep
                   (rel_expr_from_rel_expr kk result_rep
                     (MFR.Atom (1, offset)) (to_r function))
             | MFR.Atom (cardinality, _) =>
                 let
                   val domain_card =
                     MFR.card_of_rep (MFNT.rep_of argument)
                   val range_rep = MFR.Atom
                     (MFU.exact_root domain_card cardinality,
                      MFS.offset_of_type offsets
                        (#2 (Type.dom_rng (MFNT.type_of function))))
                 in
                   to_apply_vect domain_card range_rep result_rep
                     (to_vect domain_card range_rep function) argument
                 end
             | MFR.Vect (1, range_rep) =>
                 to_guard [argument] result_rep
                   (rel_expr_from_rel_expr kk result_rep range_rep
                     (to_r function))
             | MFR.Vect (count, range_rep) =>
                 to_apply_vect count range_rep result_rep
                   (to_r function) argument
             | MFR.Func (domain, MFR.Formula MFU.Neut) =>
                 to_guard [argument] result_rep
                   (rel_expr_from_formula kk result_rep
                     (kk_subset (to_opt domain argument)
                       (to_r function)))
             | MFR.Func (domain, range) =>
                 let
                   val result = rel_expr_from_rel_expr kk result_rep range
                     (kk_n_fold_join kk true domain range
                       (to_opt domain argument) (to_r function))
                 in
                   if MFR.body_rep range = MFR.Formula MFU.Neut then
                     to_guard [argument] result_rep result
                   else
                     result
                 end
             | _ => raise MFNT.NUT
                 ("Refute_ModelFinder_Kodkod.to_apply", [function]))

    and to_apply_vect count range_rep result_rep function_rel argument =
      let
        val argument_rep = MFR.one_rep offsets (MFNT.type_of argument)
          (MFR.unopt_rep (MFNT.rep_of argument))
        val vector = vect_from_rel_expr kk count result_rep
          (MFR.Vect (count, range_rep)) function_rel
        val values = unpack_vect_in_chunks kk
          (MFR.arity_of_rep result_rep) count vector
      in
        kk_case_switch kk argument_rep result_rep
          (to_opt argument_rep argument)
          (all_singletons_for_rep argument_rep) values
      end

    and to_could_be_unrep negative candidate =
      if negative andalso MFR.is_opt_rep (MFNT.rep_of candidate) then
        kk_no (to_r candidate)
      else
        KK.False

    and to_compare_with_unrep candidate relation =
      if MFR.is_opt_rep (MFNT.rep_of candidate) then
        kk_rel_if (kk_some (to_r candidate)) relation
          (empty_rel_for_rep (MFNT.rep_of candidate))
      else
        relation
  in
    to_f_with_polarity MFU.Pos nut
  end

type problem_metadata =
  {free_names : nut list,
   sel_names : nut list,
   nonsel_names : nut list,
   rel_table : nut MFNT.NameTable.table,
   unsound : bool,
   scope : MFS.scope}

type rich_problem = KK.problem * problem_metadata

type assembly_params =
  {debug : bool,
   peephole_optim : bool,
   total_consts : bool,
   datatype_sym_break : int,
   comment : string,
   settings : KK.setting list,
   free_names : nut list,
   nonsel_names : nut list,
   nondef_us : nut list,
   def_us : nut list}

fun scope_with_offsets
      ({hol_ctxt, card_assigns, bits, bisim_depth, data_types, ...}
       : MFS.scope) offsets : MFS.scope =
  {hol_ctxt = hol_ctxt, card_assigns = card_assigns, bits = bits,
   bisim_depth = bisim_depth, data_types = data_types, ofs = offsets}

fun assemble_problem_once
      ({debug, peephole_optim, total_consts, datatype_sym_break,
        comment, settings, free_names, nonsel_names, nondef_us, def_us}
       : assembly_params) unsound (scope : MFS.scope) : rich_problem =
  let
    val offsets = #ofs scope
    val data_types = #data_types scope
    val bits = #bits scope
    val main_j0 = MFS.offset_of_type offsets Type.bool
    val (nat_card, nat_j0) = MFS.spec_of_type scope MFH.num_type
    val (int_card, int_j0) = MFS.spec_of_type scope MFH.int_type
    val _ =
      if nat_j0 = main_j0 andalso int_j0 = main_j0 then ()
      else raise MFU.BAD
        ("Refute_ModelFinder_Kodkod.assemble_problem", "bad offsets")
    val kk = MFP.kodkod_constrs peephole_optim nat_card int_card main_j0
    val (free_names, rep_table) = MFNT.choose_reps_for_free_vars scope
      free_names MFNT.NameTable.empty
    val (sel_names, rep_table) =
      MFNT.choose_reps_for_all_sels scope rep_table
    (* Selector/discriminator names occur inside Construct nuts and are
       therefore seen by the generic name collector as constants.  They
       must not be chosen and renamed a second time as ordinary constants. *)
    val nonsel_names = List.filter (fn name =>
      not (List.exists (fn selector =>
        MFNT.name_ord (name, selector) = EQUAL) sel_names)) nonsel_names
    val (nonsel_names, rep_table) = MFNT.choose_reps_for_consts scope
      total_consts nonsel_names rep_table

    fun largest_rep name (guilty, arity, universe) =
      let
        val representation = MFNT.rep_of name
        val candidate = MFR.arity_of_rep representation
      in
        (if candidate > arity then MFNT.nickname_of name else guilty,
         Int.max (arity, candidate),
         Int.max (universe, MFR.min_univ_card_of_rep representation))
      end
    val initial_universe = univ_card nat_card int_card main_j0 [] KK.True
    val (guilty, highest_rep_arity, minimum_universe) =
      List.foldl (fn (name, result) => largest_rep name result)
        ("", 1, initial_universe)
        (free_names @ sel_names @ nonsel_names)
    val _ = check_arity guilty minimum_universe highest_rep_arity

    val def_us = map (MFNT.choose_reps_in_nut scope unsound rep_table true)
      def_us
    val nondef_us = map
      (MFNT.choose_reps_in_nut scope unsound rep_table false) nondef_us
    val (free_rels, pool, rel_table) = MFNT.rename_free_vars free_names
      MFP.initial_pool MFNT.NameTable.empty
    val (sel_rels, pool, rel_table) = MFNT.rename_free_vars sel_names
      pool rel_table
    val (other_rels, pool, rel_table) = MFNT.rename_free_vars nonsel_names
      pool rel_table
    val def_us = map (MFNT.rename_vars_in_nut pool rel_table) def_us
    val nondef_us = map (MFNT.rename_vars_in_nut pool rel_table) nondef_us
    val def_fs = map (kodkod_formula_from_nut offsets kk) def_us
    val nondef_fs = map (kodkod_formula_from_nut offsets kk) nondef_us
    val formula = List.foldl (fn (formula, result) =>
      MFP.s_and result formula) KK.True (def_fs @ nondef_fs)

    val plain_rels = free_rels @ other_rels
    val plain_bounds = map (bound_for_plain_rel debug) plain_rels
    val plain_axioms = map (declarative_axiom_for_plain_rel kk) plain_rels
    val need_values = empty_need_values data_types
    val sel_bounds = map
      (bound_for_sel_rel debug need_values data_types) sel_rels
    val datatype_axioms = declarative_axioms_for_data_types
      (#hol_ctxt scope) datatype_sym_break bits offsets kk rel_table
      data_types
    val declarative_axioms = plain_axioms @ datatype_axioms
    val universe_card = Int.max
      (univ_card nat_card int_card main_j0
         (plain_bounds @ sel_bounds) formula,
       if bits = 0 then 0 else main_j0 + bits + 1)
    val (built_in_bounds, built_in_axioms) =
      bounds_and_axioms_for_built_in_rels_in_formulas debug universe_card
        nat_card int_card main_j0 (formula :: declarative_axioms)
    val bounds = built_in_bounds @ plain_bounds @ sel_bounds
    val bounds = if debug then bounds else merge_bounds bounds
    val axioms = built_in_axioms @ declarative_axioms
    val highest_bound_arity = List.foldl (fn ((declarations, _), result) =>
      List.foldl (fn (((arity, _), _), maximum) =>
        Int.max (arity, maximum)) result declarations) 0 bounds
    val formula = List.foldr (fn (axiom, result) =>
      MFP.s_and axiom result) formula axioms
    val _ =
      if formula = KK.False then ()
      else check_arity "" universe_card highest_bound_arity
    val problem : KK.problem =
      {comment = (if unsound then "unsound" else "sound") ^ "\n" ^ comment,
       settings = settings, univ_card = universe_card, tuple_assigns = [],
       bounds = bounds,
       int_bounds = if bits = 0 then sequential_int_bounds universe_card
         else pow_of_two_int_bounds bits main_j0,
       expr_assigns = [], formula = formula}
    val metadata : problem_metadata =
      {free_names = free_names, sel_names = sel_names,
       nonsel_names = nonsel_names, rel_table = rel_table,
       unsound = unsound, scope = scope}
  in
    (problem, metadata)
  end

fun assemble_problem params unsound scope =
  with_arity_retry (#ofs scope) (fn offsets =>
    assemble_problem_once params unsound (scope_with_offsets scope offsets))

fun assemble_problem_pair params scope =
  (assemble_problem params false scope, assemble_problem params true scope)

(* Upstream to_set_bool_op and kk_vect_set_bool_op are dead under the M3
   closure proof and are intentionally omitted (PLAN_M3 decision 31). *)

end
