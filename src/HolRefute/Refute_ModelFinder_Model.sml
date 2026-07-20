(*  Title:      HolRefute/Refute_ModelFinder_Model.sml
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009, 2010

Model reconstruction for the HOL4 Refute model finder, including M4
specialization display. *)

signature REFUTE_MODEL_FINDER_MODEL = sig
  type term = Term.term
  type hol_type = Type.hol_type
  type rep = Refute_ModelFinder_Rep.rep
  type nut = Refute_ModelFinder_Nut.nut
  type scope = Refute_ModelFinder_Scope.scope
  type raw_bound = Refute_Forl.raw_bound

  type reconstruction =
    {bindings : (term * term) list,
     evals : (term * term) list,
     skolems : (string * term) list,
     consts : (term * string * term) list,
     types : (hol_type * term list * bool) list,
     codatatypes_ok : bool}

  datatype verdict = Keep of Refute_Core.counterexample | Drop

  val term_for_rep :
    {scope : scope,
     atoms : (hol_type option * string list) list,
     sel_names : nut list,
     rel_table : nut Refute_ModelFinder_Nut.NameTable.table,
     bounds : raw_bound list,
     maybe_opt : bool,
     ty : hol_type,
     representation : rep,
     tuples : int list list} -> term

  val user_friendly_const :
    Refute_ModelFinder_HOL.special_fun list -> string -> hol_type -> term

  val bisimilar_values :
    hol_type list -> int -> term * term -> bool

  val reconstruct :
    {scope : scope,
     atoms : (hol_type option * string list) list,
     special_funs : Refute_ModelFinder_HOL.special_fun list,
     real_frees : term list,
     eval_terms : term list,
     free_names : nut list,
     sel_names : nut list,
     nonsel_names : nut list,
     rel_table : nut Refute_ModelFinder_Nut.NameTable.table,
     bounds : raw_bound list} -> reconstruction

  val model_report : reconstruction -> Refute_Core.model_report
  val assignment_operator : string -> string
  val certification_env :
    (term * term) list -> (term * term) list option
  val certifiable : bool -> (term * term) list -> bool
  val genuine_means_genuine :
    {got_all_mono_user_axioms : bool,
     no_poly_user_axioms : bool,
     wfs : bool list,
     sound_finitizes : bool,
     total_consts : bool option} -> bool
  val try_again_reasons : string list -> string list
  val certify :
    {executable : bool,
     original : term,
     eval_terms : term list,
     reconstruction : reconstruction,
     cex : Refute_Core.counterexample,
     sound : bool,
     genuine_means_genuine : bool,
     reasons : string list} -> verdict
end

structure Refute_ModelFinder_Model
  :> REFUTE_MODEL_FINDER_MODEL = struct

open Feedback

structure MFH = Refute_ModelFinder_HOL
structure MFN = Refute_ModelFinder_Names
structure MFNT = Refute_ModelFinder_Nut
structure MFP = Refute_ModelFinder_Peephole
structure MFR = Refute_ModelFinder_Rep
structure MFS = Refute_ModelFinder_Scope
structure MFU = Refute_ModelFinder_Util

type term = Term.term
type hol_type = Type.hol_type
type rep = MFR.rep
type nut = MFNT.nut
type scope = MFS.scope
type raw_bound = Refute_Forl.raw_bound

type reconstruction =
  {bindings : (term * term) list,
   evals : (term * term) list,
   skolems : (string * term) list,
   consts : (term * string * term) list,
   types : (hol_type * term list * bool) list,
   codatatypes_ok : bool}

datatype verdict = Keep of Refute_Core.counterexample | Drop

(* Per-type running counters plus the numbers already handed out, so
   that numbering an atom is a pair of lookups rather than a scan. *)
type atom_pool =
  {counts : (hol_type, int) Redblackmap.dict,
   numbers : (hol_type * int, int) Redblackmap.dict} ref

fun new_atom_pool () : atom_pool =
  ref {counts = Redblackmap.mkDict Type.compare,
       numbers = Redblackmap.mkDict
         (Portable.pair_compare (Type.compare, Int.compare))}

type context =
  {scope : scope,
   atoms : (hol_type option * string list) list,
   sel_names : nut list,
   rel_table : nut MFNT.NameTable.table,
   bounds : raw_bound list,
   pool : atom_pool}

fun err function message =
  Feedback.mk_HOL_ERR "Refute_ModelFinder_Model" function message

fun same_type left right = Type.compare (left, right) = EQUAL

fun member_tuple tuple = List.exists (fn other => other = tuple)

fun chop count values =
  let
    fun split 0 front rest = (rev front, rest)
      | split _ front [] = (rev front, [])
      | split remaining front (value :: rest) =
          split (remaining - 1) (value :: front) rest
  in
    if count < 0 then raise err "chop" "negative count"
    else split count [] values
  end

fun find_name names nickname =
  List.find (fn name => MFNT.nickname_of name = nickname) names

fun tuples_for_name ({rel_table, bounds, ...} : context) name =
  let val relation = MFNT.the_rel rel_table name
  in Option.getOpt (AList.lookup (op =) bounds relation, []) end
  handle MFNT.NUT _ => [[]]

fun tuples_for_nickname (context as {sel_names, ...} : context) nickname =
  case find_name sel_names nickname of
      SOME name => tuples_for_name context name
    | NONE => []

fun type_atom_names atoms ty =
  case List.find (fn (pattern, _) =>
         case pattern of
             SOME pattern_ty =>
               same_type pattern_ty ty orelse
               Lib.can (Type.match_type pattern_ty) ty
           | NONE => false) atoms of
      SOME (_, names) => names
    | NONE =>
        (case List.find (fn (pattern, _) => not (Option.isSome pattern))
                        atoms of
             SOME (_, names) => names
           | NONE => [])

fun atom_number (pool : atom_pool) ty atom =
  let val {counts, numbers} = !pool in
    case Redblackmap.peek (numbers, (ty, atom)) of
        SOME number => number
      | NONE =>
          let
            val number = 1 + Option.getOpt (Redblackmap.peek (counts, ty), 0)
            val _ = pool :=
              {counts = Redblackmap.insert (counts, ty, number),
               numbers = Redblackmap.insert (numbers, (ty, atom), number)}
          in
            number
          end
  end

fun atom_term ({atoms, pool, ...} : context) ty atom =
  let
    val number = atom_number pool ty atom
    val overrides = type_atom_names atoms ty
  in
    if number <= length overrides then
      Term.mk_var (List.nth (overrides, number - 1), ty)
    else
      MFN.fake_atom number ty
  end

(* Schwartzian transform: one pretty-printer call per element instead of
   two per comparison.  Listsort.sort is not stable, so the original
   position is carried along as a tie-break; that reproduces exactly the
   order of the insertion sort this replaces. *)
fun sort_terms pairs =
  let
    fun tag _ [] = []
      | tag index ((pair as (term, _)) :: rest) =
          (Parse.term_to_string term, index, pair) :: tag (index + 1) rest
    fun compare ((left_key, left_index, _), (right_key, right_index, _)) =
      case String.compare (left_key, right_key) of
          EQUAL => Int.compare (left_index, right_index)
        | other => other
  in
    map #3 (Listsort.sort compare (tag 0 pairs))
  end

fun is_unknown term =
  Term.is_var term andalso #1 (Term.dest_var term) = "?"

fun make_update (point, value) base =
  Term.mk_comb (combinSyntax.mk_update (point, value), base)

fun make_fun ({scope, ...} : context) actual_domain_ty
      display_domain_ty display_range_ty pairs =
  let
    val complete = MFS.is_complete_type (#data_types scope) false
      actual_domain_ty
    val marker =
      if complete then MFN.irrelevant_marker display_range_ty
      else MFN.unknown_marker display_range_ty
    val base = combinSyntax.mk_K_1 (marker, display_domain_ty)
    val determined = List.filter (not o is_unknown o #2) pairs
  in
    List.foldl (fn (pair, result) => make_update pair result)
      base (sort_terms determined)
  end

fun make_set ({scope, ...} : context) maybe_opt actual_element_ty
      display_element_ty pairs =
  let
    val present = map #1 (List.filter
      (fn (_, value) => Term.aconv value boolSyntax.T) pairs)
    val all_unknown = not (null pairs) andalso List.all
      (fn (_, value) =>
        not (Term.aconv value boolSyntax.T) andalso
        not (Term.aconv value boolSyntax.F)) pairs
    val incomplete =
      not (MFS.is_complete_type (#data_types scope) false actual_element_ty)
    val elements =
      if maybe_opt andalso incomplete then
        present @ [MFN.unrepresented_marker_ascii display_element_ty]
      else
        present
    fun insert (element, set) = pred_setSyntax.mk_insert (element, set)
  in
    if all_unknown then
      MFN.unknown_marker (pred_setSyntax.mk_set_type display_element_ty)
    else
      List.foldr insert (pred_setSyntax.mk_empty display_element_ty) elements
  end

fun make_fun_or_set context maybe_opt ty pairs =
  let
    val (domain_ty, _) = Type.dom_rng ty
    val display_ty = MFH.uniterize_unarize_unbox_etc_type ty
    val (display_domain_ty, display_range_ty) = Type.dom_rng display_ty
  in
    if pred_setSyntax.is_set_type ty then
      make_set context maybe_opt domain_ty display_domain_ty pairs
    else
      make_fun context domain_ty display_domain_ty display_range_ty pairs
  end

fun factor_types ty =
  if MFH.is_pair_type ty then
    let val (left, right) = pairSyntax.dest_prod ty
    in factor_types left @ factor_types right end
  else
    [ty]

fun rebuild_value ty values =
  if MFH.is_pair_type ty then
    let
      val (left_ty, right_ty) = pairSyntax.dest_prod ty
      val (left, values) = rebuild_value left_ty values
      val (right, values) = rebuild_value right_ty values
    in
      (pairSyntax.mk_pair (left, right), values)
    end
  else
    case values of
        value :: rest => (value, rest)
      | [] => raise err "rebuild_value" "not enough selector values"

fun reconstruct_term (context as {scope, sel_names, ...} : context)
      maybe_opt ty representation tuples =
  let
    val {card_assigns, bits, data_types, ofs, ...} = scope

    fun value_of_bits tuples =
      let
        val offset = MFS.offset_of_type ofs MFH.unsigned_bit_type
        fun bit_value [atom] =
              let val index = atom - offset
                  val power = MFU.reasonable_power 2 index
              in if index = bits then ~power else power end
          | bit_value _ = raise err "value_of_bits" "malformed bit tuple"
      in
        List.foldl (fn (tuple, total) => bit_value tuple + total) 0 tuples
      end

    fun term_for_rep maybe_opt seen ty representation tuples =
      case (representation, tuples) of
          (MFR.Any, _) => MFN.unknown_marker
            (MFH.uniterize_unarize_unbox_etc_type ty)
        | (MFR.Formula _, _) =>
            if null tuples then boolSyntax.F else boolSyntax.T
        | (MFR.Atom (card, offset), [[atom]]) =>
            if atom < offset orelse atom >= offset + card then
              raise MFR.REP ("Refute_ModelFinder_Model.term_for_rep",
                             [representation])
            else
              term_for_atom seen ty (atom - offset) card
        | (MFR.Struct [left_rep, right_rep], [tuple]) =>
            if not (MFH.is_pair_type ty) then
              raise err "term_for_rep" "Struct used for a non-product"
            else
              let
                val (left_ty, right_ty) = pairSyntax.dest_prod ty
                val (left_tuple, right_tuple) =
                  chop (MFR.arity_of_rep left_rep) tuple
                val left = term_for_rep true seen left_ty left_rep
                  [left_tuple]
                val right = term_for_rep true seen right_ty right_rep
                  [right_tuple]
              in
                pairSyntax.mk_pair (left, right)
              end
        | (MFR.Vect (card, range_rep), [tuple]) =>
            let
              val (domain_ty, range_ty) = Type.dom_rng ty
              val width = MFR.arity_of_rep range_rep
              val chunks = MFU.chunk_list width tuple
              val domains = List.tabulate (card, fn atom =>
                term_for_atom seen domain_ty atom card)
              val ranges = map (fn chunk =>
                term_for_rep true seen range_ty range_rep [chunk]) chunks
            in
              if length domains <> length ranges then
                raise err "term_for_rep" "malformed vector tuple"
              else
                make_fun_or_set context true ty
                  (ListPair.zip (domains, ranges))
            end
        | (MFR.Func (domain_rep, MFR.Formula _), _) =>
            let
              val (domain_ty, _) = Type.dom_rng ty
              val combinations = MFR.all_combinations_for_rep domain_rep
              val domains = map (fn tuple =>
                term_for_rep true seen domain_ty domain_rep [tuple])
                combinations
              val ranges = map (fn tuple =>
                if member_tuple tuple tuples then boolSyntax.T
                else boolSyntax.F) combinations
            in
              make_fun_or_set context maybe_opt ty
                (ListPair.zip (domains, ranges))
            end
        | (MFR.Func (domain_rep, range_rep), _) =>
            let
              val (domain_ty, range_ty) = Type.dom_rng ty
              val domain_width = MFR.arity_of_rep domain_rep
              val combinations = MFR.all_combinations_for_rep domain_rep
              (* Chop once and index by prefix, rather than re-chopping
                 every tuple for every combination. *)
              val tail_table = List.foldl
                (fn ((prefix, tail), table) =>
                   Redblackmap.insert (table, prefix,
                     tail :: Option.getOpt
                       (Redblackmap.peek (table, prefix), [])))
                (Redblackmap.mkDict (Portable.list_compare Int.compare))
                (map (chop domain_width) tuples)
              fun tails tuple =
                rev (Option.getOpt (Redblackmap.peek (tail_table, tuple), []))
              val domains = map (fn tuple =>
                term_for_rep false seen domain_ty domain_rep [tuple])
                combinations
              val ranges = map (fn tuple =>
                term_for_rep false seen range_ty range_rep (tails tuple))
                combinations
            in
              make_fun_or_set context maybe_opt ty
                (ListPair.zip (domains, ranges))
            end
        | (MFR.Opt inner, []) => MFN.unknown_marker
            (MFH.uniterize_unarize_unbox_etc_type ty)
        | (MFR.Opt inner, _) => term_for_rep true seen ty inner tuples
        | _ => raise err "term_for_rep"
            ("cannot decode " ^ MFR.string_for_rep representation ^
             " from " ^ Int.toString (length tuples) ^ " tuples")

    and term_for_atom seen ty atom card =
      case Lib.total Type.dom_rng ty of
          SOME (domain_ty, range_ty) =>
            let
              val domain_card = MFH.card_of_type card_assigns domain_ty
              val range_card = MFH.card_of_type card_assigns range_ty
              val range_rep = MFR.Atom (range_card, 0)
              val tuple = MFU.nth_combination
                (MFU.replicate_list domain_card [(range_card, 0)]) atom
            in
              term_for_rep true seen ty
                (MFR.Vect (domain_card, range_rep)) [tuple]
            end
        | NONE =>
            if MFH.is_pair_type ty then
              let
                val (left_ty, right_ty) = pairSyntax.dest_prod ty
                val left_card = MFH.card_of_type card_assigns left_ty
                val right_card = card div left_card
                val left = term_for_atom seen left_ty
                  (atom div right_card) left_card
                val right = term_for_atom seen right_ty
                  (atom mod right_card) right_card
              in
                pairSyntax.mk_pair (left, right)
              end
            else if MFH.is_boolean_type ty then
              if atom = 0 then boolSyntax.F else boolSyntax.T
            else if MFH.is_iterator_type ty then
              numSyntax.term_of_int (card - atom - 1)
            else if same_type ty MFH.num_type then
              numSyntax.term_of_int atom
            else if same_type ty MFH.int_type then
              intSyntax.term_of_int
                (Arbint.fromInt (MFP.int_for_atom (card, 0) atom))
            else
              case MFS.data_type_spec data_types ty of
                  SOME spec =>
                    if #deep spec andalso not (null (#constrs spec)) then
                      term_for_data_type seen spec atom
                    else
                      atom_term context ty atom
                | NONE => atom_term context ty atom

    and term_for_data_type seen (spec : MFS.data_type_spec) atom =
      let
        val ty = #typ spec
        val co = #co spec
        val cycle = Term.mk_var
          (MFN.reserved_prefix ^ "cycle" ^ Int.toString atom, ty)
        val real_atom = atom + MFS.offset_of_type ofs ty
        fun name_for nickname =
          List.find (fn name =>
            MFNT.nickname_of name = nickname andalso
            same_type (#1 (Type.dom_rng (MFNT.type_of name))) ty) sel_names
        fun discriminator constructor =
          MFN.discr_prefix ^ MFH.constructor_name constructor
        fun is_constructor ({const, ...} : MFS.constr_spec) =
          case name_for (discriminator const) of
              SOME name =>
                member_tuple [real_atom] (tuples_for_name context name)
            | NONE => false
        val constructor_spec =
          case List.find is_constructor (#constrs spec) of
              SOME found => found
            | NONE => raise err "term_for_data_type"
                "no discriminator selected a constructor"
        val constructor = #const constructor_spec
        val constructor_id = MFH.constructor_name constructor
        val argument_tys = MFH.constructor_arg_types constructor
        val flat_tys = List.concat (map factor_types argument_tys)

        fun selector_info index =
          let
            val nickname = MFN.sel_prefix_for index ^ constructor_id
            val name =
              case name_for nickname of
                  SOME found => found
                | NONE => raise err "term_for_data_type"
                    ("missing selector " ^ nickname)
            val selected = List.mapPartial
              (fn owner :: rest =>
                    if owner = real_atom then SOME rest else NONE
                | [] => NONE)
              (tuples_for_name context name)
          in
            (name, selected)
          end

        fun selector_value next_seen (index, argument_ty) =
          let
            val (name, selected) = selector_info index
            val range_rep = #2 (MFR.dest_Func (MFNT.rep_of name))
          in
            term_for_rep true next_seen argument_ty range_rep selected
          end
        fun safe_the body =
          let
            val omega = Term.mk_var (MFN.cyclic_co_val_name, ty)
            val unfolded = Term.subst [{redex = cycle, residue = omega}] body
            val predicate = Term.mk_abs
              (omega, boolSyntax.mk_eq (omega, unfolded))
            val choice = Term.mk_thy_const
              {Thy = "refute", Name = "safe_The",
               Ty = Type.-->(Type.-->(ty, Type.bool), ty)}
          in
            Term.mk_comb (choice, predicate)
          end
      in
        if co andalso List.exists (fn entry => entry = (ty, atom)) seen then
          cycle
        else if MFH.is_bitword_type ty then
          let
            val value = value_of_bits (#2 (selector_info 0))
          in
            if ty = MFH.unsigned_bitword_type then
              numSyntax.term_of_int value
            else
              intSyntax.term_of_int (Arbint.fromInt value)
          end
        else
          let
            val next_seen = if co then (ty, atom) :: seen else seen
            val flat_values = map (selector_value next_seen)
              (ListPair.zip
                (List.tabulate (length flat_tys, fn index => index), flat_tys))
            fun rebuild (argument_ty, (arguments, values)) =
              let val (argument, values) = rebuild_value argument_ty values
              in (argument :: arguments, values) end
            val (arguments, remaining) =
              List.foldl rebuild ([], flat_values) argument_tys
            val _ = if null remaining then () else
              raise err "term_for_data_type" "unused selector values"
            val value = Term.list_mk_comb (constructor, rev arguments)
          in
            if co andalso Term.free_in cycle value then safe_the value
            else value
          end
      end
  in
    MFH.unarize_unbox_etc_term
      (term_for_rep maybe_opt [] ty representation tuples)
  end

fun term_for_rep {scope, atoms, sel_names, rel_table, bounds, maybe_opt,
                  ty, representation, tuples} =
  reconstruct_term
    {scope = scope, atoms = atoms, sel_names = sel_names,
     rel_table = rel_table, bounds = bounds, pool = new_atom_pool ()}
    maybe_opt ty representation tuples

fun same_free name ty term =
  case Lib.total Term.dest_var term of
      SOME (other, other_ty) => name = other andalso same_type ty other_ty
    | NONE => false

fun free_name_for_term free_names term =
  let val (name, ty) = Term.dest_var term
  in
    case List.find (fn candidate =>
           case candidate of
               MFNT.FreeName (other, other_ty, _) =>
                 name = other andalso
                 same_type (MFH.unarize_unbox_etc_type ty)
                   (MFH.unarize_unbox_etc_type other_ty)
             | _ => false) free_names of
        SOME found => found
      | NONE => MFNT.FreeName (name, ty, MFR.Any)
  end

fun uncurry_info generated_name =
  if String.isPrefix MFN.uncurry_prefix generated_name then
    let
      val suffix = String.extract
        (generated_name, size MFN.uncurry_prefix, NONE)
      val (marker, original) = MFN.strip_first_name_sep suffix
      val (count_text, at_suffix) =
        Substring.position "@" (Substring.full marker)
      val count = Int.fromString (Substring.string count_text)
      val prefix =
        if Substring.isEmpty at_suffix then NONE
        else Int.fromString
          (Substring.string (Substring.triml 1 at_suffix))
    in
      case (count, prefix) of
          (SOME count, SOME prefix) => SOME (count, prefix, original)
        | _ => NONE
    end
  else NONE

fun dest_n_tuple_type 1 ty = [ty]
  | dest_n_tuple_type count ty =
      if count > 1 andalso MFH.is_pair_type ty then
        let val (left, right) = pairSyntax.dest_prod ty
        in left :: dest_n_tuple_type (count - 1) right end
      else
        raise err "dest_n_tuple_type" "malformed uncurried tuple type"

fun user_friendly_const special_funs name ty =
  let
    val display_ty = MFH.uniterize_unarize_unbox_etc_type ty
    fun special_bounds terms =
      let
        fun schematic variable =
          case Lib.total Term.dest_var variable of
              SOME (variable_name, _) =>
                String.isPrefix (MFN.reserved_prefix ^ "v") variable_name
                orelse MFN.is_bound_var_name variable_name
                orelse MFN.is_cong_var_name variable_name
            | NONE => false
        fun add (variable, result) =
          if schematic variable andalso
             not (List.exists (Term.aconv variable) result) then
            variable :: result
          else result
      in
        Listsort.sort Term.compare
          (List.foldl add [] (List.concat (map Term.free_vars_lr terms)))
      end
    fun same_generated special =
      case Lib.total Term.dest_var special of
          SOME (special_name, special_ty) =>
            name = special_name andalso
            MFH.uniterize_unarize_unbox_etc_type ty =
              MFH.uniterize_unarize_unbox_etc_type special_ty
        | NONE => false
    fun friendly_term candidate =
      if Term.is_abs candidate then
        let val (variable, body) = Term.dest_abs candidate
        in Term.mk_abs (variable, friendly_term body) end
      else if Term.is_comb candidate then
        let val (function, argument) = Term.dest_comb candidate
        in MFH.s_betapply (friendly_term function, friendly_term argument) end
      else
        case Lib.total Term.dest_var candidate of
            SOME (candidate_name, candidate_ty) =>
              if MFN.is_reserved_name candidate_name then
                user_friendly_const special_funs candidate_name candidate_ty
              else candidate
          | NONE => candidate
    fun uncurried_friendly count prefix original =
      let
        val (argument_tys, result_ty) = boolSyntax.strip_fun display_ty
        val before_tys = List.take (argument_tys, prefix)
        val tuple_ty = List.nth (argument_tys, prefix)
        val tuple_tys = dest_n_tuple_type count tuple_ty
        val after_tys = List.drop (argument_tys, prefix + 1)
        val _ = if length tuple_tys = count then ()
          else raise err "user_friendly_const" "bad uncurry arity"
        val original_ty = boolSyntax.list_mk_fun
          (before_tys @ tuple_tys @ after_tys, result_ty)
      in
        user_friendly_const special_funs original original_ty
      end
  in
    case uncurry_info name of
        SOME (count, prefix, original) =>
          uncurried_friendly count prefix original
      | NONE => if MFN.is_quot_normal_name name then
      Term.mk_var (MFN.reserved_prefix ^ "qn", display_ty)
    else if MFN.is_unrolled_name name then
      let
        val (_, predicate_ty) = Type.dom_rng display_ty
        val original = MFN.original_name name
        val predicate = user_friendly_const special_funs original predicate_ty
        val iterator = Term.mk_var (MFN.iter_var_prefix, MFH.num_type)
      in
        Term.mk_abs (iterator, predicate)
      end
    else if MFN.is_base_name name orelse MFN.is_step_name name then
      let
        val original = MFN.original_name name
        val (_, short_name) = MFN.strip_first_name_sep original
        val stem = if short_name = "" then original else short_name
        val suffix = if MFN.is_base_name name then ".base" else ".step"
      in
        Term.mk_var (stem ^ suffix, display_ty)
      end
    else if MFN.is_special_name name then
      case List.find (same_generated o #2) special_funs of
          SOME ((original, fixed_indices, fixed_terms), _) =>
            let
              val maximum = List.foldl Int.max (~1) fixed_indices
              val (argument_types, _) =
                boolSyntax.strip_fun (Term.type_of original)
              val missing_indices = List.filter (fn index =>
                not (List.exists (fn fixed => fixed = index)
                  fixed_indices)) (MFU.index_seq 0 (maximum + 1))
              val missing_vars = ListPair.map (fn (index, argument_ty) =>
                Term.mk_var ("arg" ^ Int.toString (index + 1), argument_ty))
                (missing_indices,
                 MFU.filter_indices missing_indices argument_types)
              fun argument index =
                case List.find (fn (fixed, _) => fixed = index)
                       (ListPair.zip (fixed_indices, fixed_terms)) of
                    SOME (_, fixed) => friendly_term fixed
                  | NONE =>
                      List.nth (missing_vars,
                        Lib.index (fn missing => missing = index)
                          missing_indices)
              val arguments = map argument
                (MFU.index_seq 0 (maximum + 1))
              val bounds = special_bounds fixed_terms
            in
              Term.list_mk_abs (bounds @ missing_vars,
                Term.list_mk_comb (original, arguments))
            end
        | NONE => Term.mk_var (name, display_ty)
    else
      let
        val original = MFN.original_name name
        val (thy_part, name_part) = MFN.strip_first_name_sep original
      in
        if thy_part <> "" andalso name_part <> "" then
          Term.mk_thy_const
            {Thy = thy_part, Name = name_part, Ty = display_ty}
        else
          Term.mk_var (original, display_ty)
      end
  end handle HOL_ERR _ => Term.mk_var (MFN.original_name name,
    MFH.uniterize_unarize_unbox_etc_type ty)

fun lhs_for_constant special_funs name ty =
  user_friendly_const special_funs name ty

fun assignment_operator name =
  if MFN.is_ubfp_name name then "≤"
  else if MFN.is_lbfp_name name then "≥"
  else "="

fun eval_index name =
  if String.isPrefix MFN.eval_prefix name then
    Int.fromString (String.extract (name, size MFN.eval_prefix, NONE))
  else
    NONE

fun is_safe_the term =
  case Lib.total Term.dest_thy_const term of
      SOME {Thy = "refute", Name = "safe_The", ...} => true
    | _ => false

fun unfold_outer_the_binders term =
  case Lib.total Term.dest_comb term of
      SOME (choice, abstraction) =>
        if is_safe_the choice andalso Term.is_abs abstraction then
          let
            val (variable, body) = Term.dest_abs abstraction
            val (left, _) = boolSyntax.dest_eq body
          in
            if Term.aconv left variable then
              unfold_outer_the_binders
                (Term.beta_conv (Term.mk_comb (abstraction, term)))
            else term
          end handle HOL_ERR _ => term
        else term
    | NONE => term

fun has_codatatype_subtype co_types ty =
  List.exists (same_type ty) co_types orelse
  (not (Type.is_vartype ty) andalso
   List.exists (has_codatatype_subtype co_types)
     (#Args (Type.dest_thy_type ty)))

fun bisimilar_values _ 0 _ = true
  | bisimilar_values co_types max_depth (left, right) =
      let
        val ty = Term.type_of left
      in
        if not (same_type ty (Term.type_of right)) then false
        else if has_codatatype_subtype co_types ty then
          let
            val (left_head, left_args) =
              HolKernel.strip_comb (unfold_outer_the_binders left)
            val (right_head, right_args) =
              HolKernel.strip_comb (unfold_outer_the_binders right)
            val next_depth = max_depth -
              (if List.exists (same_type ty) co_types then 1 else 0)
          in
            Term.aconv left_head right_head andalso
            ListPair.allEq
              (bisimilar_values co_types next_depth)
              (left_args, right_args)
          end
        else
          Term.aconv left right
      end

fun reconstruct {scope, atoms, special_funs, real_frees, eval_terms,
                 free_names, sel_names, nonsel_names, rel_table, bounds} =
  let
    val context =
      {scope = scope, atoms = atoms, sel_names = sel_names,
       rel_table = rel_table, bounds = bounds, pool = new_atom_pool ()}

    fun decode name =
      case MFNT.rep_of name of
          MFR.Any => MFN.unknown_marker
            (MFH.uniterize_unarize_unbox_etc_type (MFNT.type_of name))
        | representation => reconstruct_term context
            (not (MFNT.is_fully_representable_set name))
            (MFNT.type_of name) representation
            (tuples_for_name context name)

    fun binding term =
      let val name = free_name_for_term free_names term
      in (term, decode name) end

    fun curry_uncurried_value nickname display_ty value =
      case uncurry_info nickname of
          NONE => value
        | SOME (count, prefix, _) =>
            let
              val (argument_tys, _) = boolSyntax.strip_fun display_ty
              fun add_variable (ty, (index, avoids, variables)) =
                let
                  val variable = Term.variant avoids
                    (Term.mk_var ("x" ^ Int.toString index, ty))
                in
                  (index + 1, variable :: avoids, variables @ [variable])
                end
              val (_, _, variables) = List.foldl add_variable
                (0, Term.all_vars value, []) argument_tys
              val before = List.take (variables, prefix)
              val tuple = List.take (List.drop (variables, prefix), count)
              val after = List.drop (variables, prefix + count)
              val body = Term.list_mk_comb
                (value, before @ [pairSyntax.list_mk_pair tuple] @ after)
            in
              MFH.eta_contract (Term.list_mk_abs (variables, body))
            end

    fun classify (name, (evals, skolems, consts)) =
      let
        val nickname = MFNT.nickname_of name
        val raw_value = decode name
        val lhs = lhs_for_constant special_funs nickname
          (MFNT.type_of name)
        val value = curry_uncurried_value nickname (Term.type_of lhs)
          raw_value
      in
        if MFNT.is_skolem_name name then
          (evals, (MFN.original_name nickname, value) :: skolems, consts)
        else
          case eval_index nickname of
              SOME index =>
                if index < length eval_terms then
                  ((List.nth (eval_terms, index), value) :: evals,
                   skolems, consts)
                else
                  (evals, skolems, consts)
            | NONE =>
                (evals, skolems,
                 (lhs, assignment_operator nickname, value) :: consts)
      end

    fun is_bisim_support name =
      let val nickname = MFNT.nickname_of name
      in
        nickname = "refute$bisim" orelse
        nickname = "refute$bisim_iterator_max"
      end

    val displayed_names = List.filter (not o is_bisim_support) nonsel_names
    val (evals, skolems, consts) =
      List.foldl classify ([], [], []) displayed_names

    fun values_for_type (spec : MFS.data_type_spec) =
      let
        val ty = #typ spec
        val card = #card spec
        val offset = MFS.offset_of_type (#ofs scope) ty
        val values = List.tabulate (card, fn index =>
          reconstruct_term context false ty (MFR.Atom (card, offset))
            [[offset + index]])
        val complete = MFU.fun_from_pair (#complete spec) false
      in
        (ty, values, complete)
      end

    val deep_types = List.filter #deep (#data_types scope)
    fun has_type ty = List.exists (fn (spec : MFS.data_type_spec) =>
      same_type (#typ spec) ty) deep_types
    fun integer_type ty =
      case MFH.assignment_lookup (#card_assigns scope) ty of
          SOME card =>
            if has_type ty then [] else
              [{typ = ty, card = card, co = false, self_rec = true,
                complete = (false, false), concrete = (true, true),
                deep = true, constrs = []} : MFS.data_type_spec]
        | NONE => []
    fun type_variable_spec (ty, card) =
      if Type.is_vartype ty andalso not (MFH.is_iterator_type ty) then
        [{typ = ty, card = card, co = false, self_rec = false,
          complete = (true, true), concrete = (true, true), deep = true,
          constrs = []} : MFS.data_type_spec]
      else
        []
    val report_types = deep_types @
      List.concat (map integer_type [MFH.num_type, MFH.int_type]) @
      List.concat (map type_variable_spec (#card_assigns scope))
    val types = map values_for_type report_types
    val codatatypes = List.filter #co (#data_types scope)
    val co_types = map #typ codatatypes
    val max_depth = List.foldl
      (fn (spec : MFS.data_type_spec, total) => #card spec + total)
      0 codatatypes
    fun distinct_pairs [] = []
      | distinct_pairs (value :: rest) =
          map (fn other => (value, other)) rest @ distinct_pairs rest
    fun wellformed (spec : MFS.data_type_spec) =
      let val (_, values, _) = values_for_type spec
      in
        List.all (not o bisimilar_values co_types max_depth)
          (distinct_pairs values)
      end
    val codatatypes_ok = #bisim_depth scope >= 0 orelse
      List.all wellformed codatatypes
  in
    {bindings = map binding real_frees,
     evals = rev evals,
     skolems = rev skolems,
     consts = rev consts,
     types = types,
     codatatypes_ok = codatatypes_ok}
  end

fun model_report ({skolems, consts, types, ...} : reconstruction) =
  {skolems = skolems, consts = consts, types = types}

fun replace_irrelevant term =
  if combinSyntax.is_K_1 term then
    let
      val body = combinSyntax.dest_K_1 term
      val (domain_ty, _) = Type.dom_rng (Term.type_of term)
    in
      if Term.is_var body andalso #1 (Term.dest_var body) = "_" then
        combinSyntax.mk_K_1 (boolSyntax.mk_arb (Term.type_of body), domain_ty)
      else
        combinSyntax.mk_K_1 (replace_irrelevant body, domain_ty)
    end
  else if Term.is_var term then
    term
  else if Term.is_abs term then
    let val (variable, body) = Term.dest_abs term
    in Term.mk_abs (variable, replace_irrelevant body) end
  else if Term.is_comb term then
    let val (function, argument) = Term.dest_comb term
    in Term.mk_comb (replace_irrelevant function,
                     replace_irrelevant argument) end
  else
    term

fun certification_env bindings =
  let
    val copied = map (fn (variable, value) =>
      (variable, replace_irrelevant value)) bindings
  in
    if List.all (null o Term.free_vars_lr o #2) copied then SOME copied
    else NONE
  end

fun rf_type card =
  Type.mk_thy_type
    {Thy = "refute", Tyop = "rf" ^ Int.toString card, Args = []}

fun rf_constructor card serial =
  Term.prim_mk_const
    {Thy = "refute", Name = "rf" ^ Int.toString card ^ "_" ^
       Int.toString serial}

(* Certification is deliberately performed on a private, monomorphic copy.
   A native goal type variable with scope cardinality k is transported to
   the static rf_k enum and its displayed fake atoms are transported to the
   corresponding constructors.  The reconstructed model itself remains
   polymorphic, so none of these rf terms escape into model display. *)
fun certification_copy scope original eval_terms bindings =
  let
    val tyvars = Lib.U (map Term.type_vars_in_term
      (original :: eval_terms @
       List.concat (map (fn (left, right) => [left, right]) bindings)))
    fun scope_card ty =
      case scope of
          SOME assignments =>
            Option.map #2 (List.find (fn (other, _) => same_type ty other)
              assignments)
        | NONE => NONE
    fun collect [] = SOME []
      | collect (tyvar :: rest) =
          (case (scope_card tyvar, collect rest) of
               (SOME card, SOME rows) =>
                 if card >= 1 andalso card <= 6 then
                   SOME ((tyvar, card) :: rows)
                 else NONE
             | _ => NONE)
    fun atom_substitutions (tyvar, card) =
      let
        val ty = rf_type card
      in
        List.tabulate (card, fn index =>
          {redex = MFN.fake_atom (index + 1) ty,
           residue = rf_constructor card (index + 1)})
      end
  in
    if null tyvars then
      Option.map (fn env =>
        {original = original, eval_terms = eval_terms, env = env,
         polymorphic = false}) (certification_env bindings)
    else
      case collect tyvars of
          NONE => NONE
        | SOME rows =>
            let
              val theta = map (fn (tyvar, card) =>
                {redex = tyvar, residue = rf_type card}) rows
              val atoms = List.concat (map atom_substitutions rows)
              fun copy_value value = Term.subst atoms
                (Term.inst theta (replace_irrelevant value))
              val env = map (fn (variable, value) =>
                (Term.inst theta variable, copy_value value)) bindings
            in
              if List.all (null o Term.free_vars_lr o #2) env then
                SOME
                  {original = Term.inst theta original,
                   eval_terms = map (Term.inst theta) eval_terms,
                   env = env, polymorphic = true}
              else NONE
            end
  end

fun certifiable executable bindings =
  executable andalso Option.isSome (certification_env bindings)

fun genuine_means_genuine
      {got_all_mono_user_axioms, no_poly_user_axioms, wfs,
       sound_finitizes, total_consts} =
  got_all_mono_user_axioms andalso no_poly_user_axioms andalso
  List.all not wfs andalso sound_finitizes andalso
  total_consts <> SOME true

fun try_again_reasons options = map (fn option =>
  "Try again with " ^ option) options

fun replace_cex (cex : Refute_Core.counterexample) certainty bindings
      evals cert model =
  {backend = #backend cex, substrate = #substrate cex,
   certainty = certainty, bindings = bindings, evals = evals,
   cert = cert, scope = #scope cex, model = model, stats = #stats cex}

fun decoded_eval evals term =
  Option.map #2 (List.find (fn (candidate, _) =>
    Term.aconv candidate term) evals)

fun merge_evals decoded exact = map (fn (term, value) =>
  if is_unknown value orelse Term.aconv value term then
    (term, Option.getOpt (decoded_eval decoded term, value))
  else
    (term, value)) exact

fun fallback_certainty sound genuine reasons =
  if sound andalso genuine then Refute_Core.Genuine
  else if sound then Refute_Core.QuasiGenuine reasons
  else Refute_Core.Potential reasons

fun certify {executable, original, eval_terms,
             reconstruction = reconstructed, cex, sound,
             genuine_means_genuine = genuine, reasons} =
  let
    val {bindings, evals, codatatypes_ok, ...} = reconstructed
    val genuine = genuine andalso codatatypes_ok
    val model = SOME (model_report reconstructed)
    val base = replace_cex cex (fallback_certainty sound genuine reasons)
      bindings evals NONE model
  in
    case if executable andalso codatatypes_ok then
           certification_copy (#scope cex) original eval_terms bindings
         else NONE of
        NONE => Keep base
      | SOME {original = cert_original, eval_terms = cert_evals,
              env, polymorphic} =>
          (case Refute_Cert.certify
              {original = cert_original, evals = cert_evals, env = env,
               cex = base} of
               Refute_Cert.Certified certified =>
                 Keep (replace_cex certified Refute_Core.Genuine bindings
                   (if polymorphic then evals
                    else merge_evals evals (#evals certified))
                   (#cert certified) model)
             | Refute_Cert.Potential potential =>
                 Keep (replace_cex potential (#certainty potential) bindings
                   evals NONE model)
             | Refute_Cert.Discarded =>
                 if sound then
                   let
                     val reason =
                       "certification refuted the model — please report"
                     val _ = Refute_Core.Private.say 1
                       ("Refute warning: " ^ reason ^ "\n")
                   in
                     Keep (replace_cex base
                       (Refute_Core.Potential [reason]) bindings evals NONE
                       model)
                   end
                 else
                   Drop)
  end

end
