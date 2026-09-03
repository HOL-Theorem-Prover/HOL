structure Refute_ModelFinder_Scope = struct
  open Portable Feedback

  type hol_type = Type.hol_type
  type term = Term.term
  type context = Refute_ModelFinder_HOL.mf_context

  structure MFH = Refute_ModelFinder_HOL
  structure Util = Refute_ModelFinder_Util

  type constr_spec =
    {const : term,
     delta : int,
     epsilon : int,
     exclusive : bool,
     explicit_max : int,
     total : bool}

  type data_type_spec =
    {typ : hol_type,
     card : int,
     co : bool,
     self_rec : bool,
     complete : bool * bool,
     concrete : bool * bool,
     deep : bool,
     constrs : constr_spec list}

  type offset_table = (hol_type, int) Redblackmap.dict * int

  type scope =
    {hol_ctxt : context,
     binarize : bool,
     card_assigns : (hol_type * int) list,
     bits : int,
     bisim_depth : int,
     data_types : data_type_spec list,
     ofs : offset_table}

  datatype row_kind = Card of hol_type | Max of term
  type row = row_kind * int list
  type block = row list
  type scope_desc =
    (hol_type * int) list * (term * int) list

  val max_scopes = 5000
  val distinct_threshold = 1000
  val sync_threshold = 5
  val linearity = 5
  val max_bits = 31

  (* pseudo_frees is deliberately absent; its only consumer hardwires the
     vestigial upstream list to []. *)

  fun err function message =
    Feedback.mk_HOL_ERR "Refute_ModelFinder_Scope" function message

  fun type_matches pattern actual =
    MFH.type_matches_unboxed (pattern, actual)

  fun type_arguments ty =
    if Type.is_vartype ty then []
    else #Args (Type.dest_thy_type ty)

  fun exists_subtype predicate ty =
    predicate ty orelse List.exists (exists_subtype predicate)
      (type_arguments ty)

  fun is_asymmetric_non_data_type ty =
    MFH.is_iterator_type ty orelse MFH.is_integer_type ty orelse
    MFH.is_bit_type ty

  fun data_type_spec (data_types : data_type_spec list) ty =
    List.find (fn spec => Util.same_type (#typ spec) ty) data_types

  fun same_constructor left right =
    MFH.constructor_name left = MFH.constructor_name right andalso
    Util.same_type (MFH.constructor_result_type left)
      (MFH.constructor_result_type right)

  fun constr_spec ([] : data_type_spec list) constructor =
      raise err "constr_spec" "constructor has no scope specification"
    | constr_spec (data_type :: data_types) constructor =
      (case List.find (fn spec =>
               same_constructor (#const spec) constructor)
              (#constrs data_type) of
           SOME spec => spec
         | NONE => constr_spec data_types constructor)

  fun is_complete_type data_types facto ty =
    case Lib.total Type.dom_rng ty of
        SOME (domain, range) =>
          is_concrete_type data_types facto domain andalso
          is_complete_type data_types facto range
      | NONE =>
          if MFH.is_pair_type ty then
            let val (left, right) = pairSyntax.dest_prod ty
            in
              is_complete_type data_types facto left andalso
              is_complete_type data_types facto right
            end
          else if is_asymmetric_non_data_type ty orelse
                  MFH.is_bitword_type ty then
            false
          else
            (case data_type_spec data_types ty of
                 SOME spec => Util.fun_from_pair (#complete spec) facto
               | NONE => true)
  and is_concrete_type data_types facto ty =
    case Lib.total Type.dom_rng ty of
        SOME (domain, range) =>
          is_complete_type data_types facto domain andalso
          is_concrete_type data_types facto range
      | NONE =>
          if MFH.is_pair_type ty then
            let val (left, right) = pairSyntax.dest_prod ty
            in
              is_concrete_type data_types facto left andalso
              is_concrete_type data_types facto right
            end
          else if MFH.is_bitword_type ty then
            true
          else
            (case data_type_spec data_types ty of
                 SOME spec => Util.fun_from_pair (#concrete spec) facto
               | NONE => true)

  fun is_exact_type data_types facto ty =
    is_complete_type data_types facto ty andalso
    is_concrete_type data_types facto ty

  fun offset_of_type (offsets, fallback) ty =
    Option.getOpt (Redblackmap.peek (offsets, ty), fallback)

  fun spec_of_type
        ({card_assigns, ofs, ...} : scope) ty =
    ((MFH.card_of_type card_assigns ty
      handle HOL_ERR _ => ~1),
     offset_of_type ofs ty)

  (* The widest word carrier of a scope, or 0 without one.  Word operations
     are computed in Kodkod's integers, so this sets the integer width the
     problem asks for. *)
  fun max_word_width ({card_assigns, ...} : scope) =
    List.foldl Int.max 0
      (List.mapPartial (MFH.word_dimension o #1) card_assigns)

  fun same_card_assigns (left, right) =
    ListPair.allEq (fn ((left_ty, left_card),
                        (right_ty, right_card)) =>
      Util.same_type left_ty right_ty andalso left_card = right_card)
      (left, right)

  fun same_constr_specs (left, right) =
    ListPair.allEq (fn (left : constr_spec, right : constr_spec) =>
      same_constructor (#const left) (#const right) andalso
      #delta left = #delta right andalso
      #epsilon left = #epsilon right andalso
      #exclusive left = #exclusive right andalso
      #explicit_max left = #explicit_max right andalso
      #total left = #total right) (left, right)

  fun same_data_type_specs (left, right) =
    ListPair.allEq (fn (left : data_type_spec,
                        right : data_type_spec) =>
      Util.same_type (#typ left) (#typ right) andalso
      #card left = #card right andalso #co left = #co right andalso
      #self_rec left = #self_rec right andalso
      #complete left = #complete right andalso
      #concrete left = #concrete right andalso
      #deep left = #deep right andalso
      same_constr_specs (#constrs left, #constrs right)) (left, right)

  fun scopes_equivalent (left : scope, right : scope) =
    same_data_type_specs (#data_types left, #data_types right) andalso
    same_card_assigns (#card_assigns left, #card_assigns right)

  fun rank_of_row (_, candidates) = length candidates

  fun rank_of_block block =
    List.foldl Int.max 1 (map rank_of_row block)

  fun project_row _ (kind, []) = (kind, [1]) (* desperate measure *)
    | project_row column (kind, candidates) =
      (kind, [List.nth (candidates,
        Int.min (column, length candidates - 1))])

  fun project_block (column, block) = map (project_row column) block

  fun lookup_ints_assign describe equal assigns key =
    case Util.triple_lookup equal assigns key of
        SOME candidates => candidates
      | NONE => raise err "lookup_ints_assign"
          ("missing assignment for " ^ describe key)

  fun lookup_type_ints_assign assigns ty =
    map (fn value => Int.max (1, value))
      (lookup_ints_assign Parse.type_to_string
         (fn (actual, pattern) => type_matches pattern actual) assigns ty)

  fun const_matches (pattern, actual) =
    case (Lib.total MFH.constructor_name pattern,
          Lib.total MFH.constructor_name actual) of
        (SOME pattern_name, SOME actual_name) =>
          pattern_name = actual_name andalso
          type_matches (Term.type_of pattern) (Term.type_of actual)
      | _ => false

  fun lookup_const_ints_assign assigns constructor =
    let
      fun exact (SOME other, _) = Term.aconv other constructor
        | exact _ = false
      fun relaxed (SOME other, _) = const_matches (other, constructor)
        | relaxed _ = false
      fun fallback (NONE, _) = true
        | fallback _ = false
    in
      case List.find exact assigns of
          SOME (_, candidates) => candidates
        | NONE =>
            (case List.find relaxed assigns of
                 SOME (_, candidates) => candidates
               | NONE =>
                   (case List.find fallback assigns of
                        SOME (_, candidates) => candidates
                      | NONE => raise err "lookup_const_ints_assign"
                          ("missing assignment for " ^
                           Parse.term_to_string constructor)))
    end

  fun explicit_iter_ints_assign assigns predicate =
    let
      fun exact (SOME other, _) = Term.aconv other predicate
        | exact _ = false
      fun relaxed (SOME other, _) = MFH.const_match (predicate, other)
        | relaxed _ = false
    in
      case List.find exact assigns of
          SOME (_, candidates) => SOME candidates
        | NONE => Option.map #2 (List.find relaxed assigns)
    end

  fun default_iter_ints_assign assigns = Option.map #2
    (List.find (fn (pattern, _) => not (Option.isSome pattern)) assigns)

  fun lookup_group_iter_ints_assign assigns predicates =
    case get_first (explicit_iter_ints_assign assigns) predicates of
        SOME candidates => candidates
      | NONE =>
          (case default_iter_ints_assign assigns of
               SOME candidates => candidates
             | NONE => raise err "lookup_group_iter_ints_assign"
                 "missing iterator assignment")

  fun row_for_constr maxes_assigns constructor =
    SOME (Max constructor,
      lookup_const_ints_assign maxes_assigns constructor)
    handle HOL_ERR _ => NONE

  fun bit_card bits = Int.min (max_bits, Int.max (1, bits))

  (* A word carrier is exact and unsearched: width [w] means exactly [2^w]
     atoms, atom [j] denoting [n2w j].  Materializing them is the whole
     cost, so an oversized width refuses by name instead of being built. *)
  val max_word_atoms = 1024

  fun word_atom_count width =
    if width <= 30 then Int.toString (Util.reasonable_power 2 width)
    else "2^" ^ Int.toString width

  fun word_card ty =
    case MFH.word_dimension ty of
        NONE => raise err "word_card" "not a word type"
      | SOME width =>
          if width > 30 orelse
             Util.reasonable_power 2 width > max_word_atoms then
            raise Util.NOT_SUPPORTED
              ("word width " ^ Int.toString width ^ " needs " ^
               word_atom_count width ^ " atoms")
          else Util.reasonable_power 2 width

  fun block_for_type context binarize cards_assigns maxes_assigns
        iters_assigns bitss bisim_depths ty =
    if MFH.is_bisim_iterator_type ty then
      [(Card ty, map (fn depth =>
          if depth < 0 then 0 else depth + 1) bisim_depths)]
    else if MFH.is_fp_iterator_type ty then
      (case MFH.iterator_info_for_type context ty of
           SOME {preds, ...} =>
             [(Card ty, map (fn count => Int.max (0, count) + 1)
               (lookup_group_iter_ints_assign iters_assigns preds))]
         | NONE => raise err "block_for_type" "unregistered iterator type")
    else if ty = MFH.unsigned_bit_type then
      [(Card ty, map bit_card bitss)]
    else if ty = MFH.signed_bit_type then
      [(Card ty, map (fn bits => bit_card bits + 1) bitss)]
    else if ty = MFH.unsigned_bitword_type then
      [(Card ty, lookup_type_ints_assign cards_assigns MFH.num_type)]
    else if ty = MFH.signed_bitword_type then
      [(Card ty, lookup_type_ints_assign cards_assigns MFH.int_type)]
    else if MFH.is_word_type ty then
      [(Card ty, [word_card ty])]
    else if MFH.is_char_type ty then
      (* Like a word carrier: exact, unsearched, atom [j] denoting [CHR j]. *)
      [(Card ty, [MFH.char_card])]
    else
      (Card ty, lookup_type_ints_assign cards_assigns ty) ::
      (case MFH.binarized_and_boxed_data_type_constrs context binarize ty of
           [_] => []
         | constructors =>
             List.mapPartial (row_for_constr maxes_assigns) constructors)

  fun blocks_for_types context binarize cards_assigns maxes_assigns
        iters_assigns bitss bisim_depths mono_types nonmono_types =
    let
      fun block_for ty =
        block_for_type context binarize cards_assigns maxes_assigns
          iters_assigns bitss bisim_depths ty
      val mono_block = List.concat (map block_for mono_types)
      val nonmono_blocks = map block_for nonmono_types
    in
      mono_block :: nonmono_blocks
    end

  fun combination_cost [] = 0
    | combination_cost [column] = column
    | combination_cost (column :: columns) =
      if column < sync_threshold andalso
         List.all (fn other => other = column) columns then
        column - sync_threshold
      else
        List.foldl (fn (value, total) =>
          total + (value + linearity) * (value + linearity))
          0 (column :: columns)

  (* Deliberately not [Portable.list_compare], which is total: a ragged
     pair here means two scopes disagree on their coordinates, which is an
     internal invariant violation rather than an ordering question. *)
  fun strict_list_compare compare ([], []) = EQUAL
    | strict_list_compare compare (left :: lefts, right :: rights) =
        (case compare (left, right) of
             EQUAL => strict_list_compare compare (lefts, rights)
           | order => order)
    | strict_list_compare _ _ = raise Util.BAD
        ("Refute_ModelFinder_Scope.strict_list_compare", "unequal lengths")

  val int_list_compare = strict_list_compare Int.compare

  (* A leftist heap of combinations, cheapest first. *)
  datatype frontier_heap =
      FrontierEmpty
    | FrontierNode of int * int list * frontier_heap * frontier_heap

  fun frontier_before left right =
    let
      val left_cost = combination_cost left
      val right_cost = combination_cost right
    in
      left_cost < right_cost orelse
      (left_cost = right_cost andalso
       int_list_compare (left, right) = LESS)
    end

  fun frontier_rank FrontierEmpty = 0
    | frontier_rank (FrontierNode (rank, _, _, _)) = rank

  fun frontier_make value left right =
    if frontier_rank left < frontier_rank right then
      FrontierNode (frontier_rank left + 1, value, right, left)
    else
      FrontierNode (frontier_rank right + 1, value, left, right)

  fun frontier_merge FrontierEmpty right = right
    | frontier_merge left FrontierEmpty = left
    | frontier_merge
        (left as FrontierNode (_, left_value, left_left, left_right))
        (right as FrontierNode (_, right_value, right_left, right_right)) =
        if frontier_before left_value right_value then
          frontier_make left_value left_left
            (frontier_merge left_right right)
        else
          frontier_make right_value right_left
            (frontier_merge left right_right)

  fun frontier_insert value heap =
    frontier_merge (FrontierNode (1, value, FrontierEmpty, FrontierEmpty))
      heap

  fun all_combinations_ordered_smartly_at_most count ranks =
    let
      fun is_synchronized combination =
        case combination of
            [] => true
          | value :: values =>
              value < sync_threshold andalso
              List.all (fn other => other = value) values
      fun baseline () = map #2 ranks
      fun valid_sync value =
        List.all (fn (rank, offset) =>
          value >= offset andalso value < offset + rank) ranks
      fun children combination =
        let
          fun build _ [] [] = []
            | build left ((rank, offset) :: ranks) (value :: values) =
                let
                  val rest_at_offsets = ListPair.allEq
                    (fn (other, (_, other_offset)) => other = other_offset)
                    (values, ranks)
                  val this =
                    if value + 1 < offset + rank andalso rest_at_offsets then
                      [rev left @ (value + 1 :: values)]
                    else []
                in
                  this @ build (value :: left) ranks values
                end
            | build _ _ _ = raise Util.BAD
                ("Refute_ModelFinder_Scope.children", "unequal lengths")
        in
          List.filter (not o is_synchronized) (build [] ranks combination)
        end
      val initial =
        if null ranks then [[]]
        else
          let
            val synced = List.mapPartial (fn value =>
              if valid_sync value then SOME (map (fn _ => value) ranks)
              else NONE) (Util.index_seq 0 sync_threshold)
            val base = baseline ()
          in
            if is_synchronized base then synced else base :: synced
          end
      fun loop 0 _ result = rev result
        | loop _ FrontierEmpty result = rev result
        | loop remaining (FrontierNode (_, combination, left, right))
            result =
            let
              val rest = frontier_merge left right
              val next = List.foldl
                (fn (child, heap) => frontier_insert child heap)
                rest (children combination)
            in
              loop (remaining - 1) next (combination :: result)
            end
    in
      if List.exists (fn (rank, _) => rank <= 0) ranks then []
      else
        loop (Int.max (0, count))
          (List.foldl
            (fn (combination, heap) => frontier_insert combination heap)
            FrontierEmpty initial) []
    end

  type combination_cursor =
    {ranks : int option list,
     heap : frontier_heap ref,
     visited : (int list, unit) Redblackmap.dict ref}

  fun coordinate_valid NONE _ = true
    | coordinate_valid (SOME rank) coordinate = coordinate < rank

  fun new_combination_cursor ranks =
    let
      fun valid combination =
        ListPair.allEq (fn (rank, coordinate) =>
          coordinate_valid rank coordinate) (ranks, combination)
      val synchronized = List.mapPartial (fn coordinate =>
        let val candidate = map (fn _ => coordinate) ranks
        in if valid candidate then SOME candidate else NONE end)
        (Util.index_seq 0 sync_threshold)
      val baseline = map (fn _ => 0) ranks
      val seeds = Lib.mk_set
        (if Lib.mem baseline synchronized then synchronized
         else baseline :: synchronized)
      val viable = not (List.exists (fn SOME rank => rank <= 0
                                      | NONE => false) ranks)
    in
      {ranks = ranks,
       heap = ref (if viable then
           List.foldl (fn (value, heap) => frontier_insert value heap)
             FrontierEmpty seeds
         else FrontierEmpty),
       visited = ref (List.foldl (fn (seed, table) =>
         Redblackmap.insert (table, seed, ()))
         (Redblackmap.mkDict int_list_compare)
         (if viable then seeds else []))}
    end

  fun combination_cursor_next
        (cursor : combination_cursor) =
    case !(#heap cursor) of
        FrontierEmpty => NONE
      | FrontierNode (_, combination, left, right) =>
          let
            val _ = #heap cursor := frontier_merge left right
            fun add_child (index, coordinate) =
              let
                val next = List.take (combination, index) @
                  (coordinate + 1 :: List.drop (combination, index + 1))
                val rank = List.nth (#ranks cursor, index)
              in
                if coordinate_valid rank (coordinate + 1) andalso
                   not (Option.isSome
                     (Redblackmap.peek (!(#visited cursor), next))) then
                  (#visited cursor := Redblackmap.insert
                     (!(#visited cursor), next, ());
                   #heap cursor := frontier_insert next (!(#heap cursor)))
                else ()
              end
            val _ = List.app add_child (Lib.enumerate 0 combination)
          in
            SOME combination
          end

  fun number_of_combinations ranks =
    List.foldl (fn ((rank, _), total) =>
      total * IntInf.fromInt (Int.max (0, rank))) (1 : IntInf.int) ranks

  fun saturated_int integer =
    case Int.maxInt of
        SOME maximum =>
          if integer > IntInf.fromInt maximum then maximum
          else IntInf.toInt integer
      | NONE => IntInf.toInt integer

  fun is_self_recursive_constr_type constructor_ty =
    let val body = #2 (boolSyntax.strip_fun constructor_ty)
    in
      List.exists (exists_subtype (Util.same_type body))
        (#1 (boolSyntax.strip_fun constructor_ty))
    end

  fun constr_max maxes constructor =
    case List.find (fn (other, _) =>
           same_constructor other constructor) maxes of
        SOME (_, maximum) => maximum
      | NONE => ~1

  (* The product of the argument cardinalities, saturating at [maximum];
     [default] stands in for an argument type without a bounded card. *)
  fun domain_card_with default maximum card_assigns constructor =
    List.foldl (fn (argument_ty, total) =>
      let
        val card = MFH.bounded_card_of_type maximum default
          card_assigns argument_ty
      in
        if total = 0 orelse card = 0 then 0
        else if total >= maximum orelse card >= maximum orelse
                total > maximum div card then maximum
        else total * card
      end) 1 (MFH.constructor_arg_types constructor)

  fun constructor_domain_card maximum = domain_card_with ~1 maximum

  fun domain_card maximum = domain_card_with maximum maximum

  fun is_surely_inconsistent_card_assign context binarize
        (card_assigns, max_assigns) (ty, card) =
    case MFH.binarized_and_boxed_data_type_constrs context binarize ty of
        [] => false
      | constructors =>
          let
            fun effective_max domain_card constructor =
              let val maximum = constr_max max_assigns constructor
              in
                if maximum = ~1 then domain_card
                else Int.min (domain_card, maximum)
              end
            val maximum = List.foldl (fn (constructor, total) =>
              total + effective_max
                (constructor_domain_card card card_assigns constructor)
                constructor) 0 constructors
          in
            maximum < card
          end

  fun is_surely_inconsistent_scope_description context binarize seen rest
        max_assigns =
    List.exists
      (is_surely_inconsistent_card_assign context binarize
        (seen @ rest, max_assigns)) seen

  fun repair_card_assigns context binarize (card_assigns, max_assigns) =
    let
      fun repair seen [] = SOME seen
        | repair _ ((_, 0) :: _) = NONE
        | repair seen ((ty, card) :: rest) =
          ((if is_surely_inconsistent_scope_description context binarize
                 ((ty, card) :: seen) rest max_assigns then
              raise Util.SAME ()
            else
              case repair ((ty, card) :: seen) rest of
                  result as SOME _ => result
                | NONE => raise Util.SAME ())
           handle Util.SAME () =>
             repair seen ((ty, card - 1) :: rest))
    in
      repair [] (rev card_assigns)
    end

  fun add_row_to_scope_descriptor (kind, candidates)
        (card_assigns, max_assigns) =
    let val value = hd candidates
    in
      case kind of
          Card ty => ((ty, value) :: card_assigns, max_assigns)
        | Max constructor =>
            (card_assigns, (constructor, value) :: max_assigns)
    end

  fun scope_descriptor_from_block block =
    List.foldr (fn (row, desc) =>
      add_row_to_scope_descriptor row desc) ([], []) block

  fun repair_iterator_assign context assigns (assign as (ty, card)) =
    if MFH.is_bisim_iterator_type ty then
      let
        val maximum = List.foldl (fn ((other, other_card), total) =>
          if MFH.is_codatatype other then total + other_card else total)
          0 assigns
      in
        (ty, Int.min (card, maximum))
      end
    else case MFH.iterator_info_for_type context ty of
        NONE => assign
      | SOME {arg_tyss, ...} =>
          let
            fun tuple_card argument_tys =
              if null argument_tys then 1
              else
                (* A disconnected member need not occur in the collected
                   equations, so its argument types may have no scope row.
                   Falling back to the proposed iterator card merely skips
                   this optional cap; every unrolling depth remains sound. *)
                MFH.bounded_card_of_type card card assigns
                  (MFH.tuple_type argument_tys)
            fun add_capped (argument_tys, total) =
              Int.min (card, total + tuple_card argument_tys)
            val maximum = List.foldl add_capped 0 arg_tyss
          in
            (ty, Int.min (card, maximum))
          end

  fun scope_descriptor_from_combination context binarize blocks columns =
    let
      val rows = List.concat
        (ListPair.map project_block (columns, blocks))
      val (card_assigns, max_assigns) =
        scope_descriptor_from_block rows
    in
      Option.map (fn repaired =>
        (map (repair_iterator_assign context repaired) repaired,
         max_assigns))
        (repair_card_assigns context binarize (card_assigns, max_assigns))
    end

  fun offset_table_for_card_assigns data_types assigns =
    let
      fun insert ty offset table =
        Redblackmap.insert (table, ty, offset)
      fun allocate next _ table [] = (table, next)
        | allocate next reusable table ((ty, card) :: rest) =
          if card = 1 orelse is_asymmetric_non_data_type ty then
            allocate next reusable table rest
          else
            (case data_type_spec data_types ty of
                 SOME spec =>
                   if length (#constrs spec) > 1 then
                     allocate (next + card) reusable
                       (insert ty next table) rest
                   else
                     reuse next reusable table ty card rest
               | NONE => reuse next reusable table ty card rest)
      and reuse next reusable table ty card rest =
        case AList.lookup (op =) reusable card of
            SOME offset =>
              allocate next reusable (insert ty offset table) rest
          | NONE =>
              allocate (next + card) ((card, next) :: reusable)
                (insert ty next table) rest
    in
      allocate 0 [] (Redblackmap.mkDict Type.compare) assigns
    end

  fun add_constr_spec (card_assigns, max_assigns) acyclic card
        sum_dom_cards num_self_recs num_non_self_recs
        (self_rec, constructor) constrs =
    let
      val maximum = constr_max max_assigns constructor
      fun next_delta () =
        if null constrs then 0 else #epsilon (hd constrs)
      val {delta, epsilon, exclusive, total} =
        if maximum = 0 then
          let val delta = next_delta ()
          in
            {delta = delta, epsilon = delta,
             exclusive = true, total = false}
          end
        else if num_self_recs > 0 then
          ((if num_non_self_recs = 1 then
              if self_rec then
                case List.last constrs of
                    {delta = 0, epsilon = 1, exclusive = true, ...} =>
                      {delta = 1, epsilon = card,
                       exclusive = num_self_recs = 1, total = false}
                  | _ => raise Util.SAME ()
              else if domain_card 2 card_assigns constructor = 1 then
                {delta = 0, epsilon = 1,
                 exclusive = acyclic, total = acyclic}
              else
                raise Util.SAME ()
            else
              raise Util.SAME ())
           handle Util.SAME () =>
             {delta = 0, epsilon = card,
              exclusive = false, total = false})
        else if card = sum_dom_cards (card + 1) then
          let val delta = next_delta ()
          in
            {delta = delta,
             epsilon = delta + domain_card card card_assigns constructor,
             exclusive = true, total = true}
          end
        else
          {delta = 0, epsilon = card,
           exclusive = num_self_recs + num_non_self_recs = 1,
           total = false}
    in
      {const = constructor, delta = delta, epsilon = epsilon,
       exclusive = exclusive, explicit_max = maximum,
       total = total} :: constrs
    end

  (* [card_of_type] reports "no exact cardinality" by raising, and a
     cardinality too large to fit in an int by TOO_LARGE; an unassigned :num
     reaches here through the constructor fields of any data type over it.
     Both answers are this predicate's own [false], as they already are in
     [MFH.bounded_card_of_type], which guards the same call. *)
  fun has_exact_card context facto finitizable_data_types
        card_assigns ty =
    let val card = MFH.card_of_type card_assigns ty
    in
      card = MFH.bounded_exact_card_of_type context
        (if facto then finitizable_data_types else [])
        (card + 1) 0 card_assigns ty
    end handle HOL_ERR _ => false
             | Refute_ModelFinder_Util.TOO_LARGE _ => false

  fun data_type_spec_from_scope_descriptor context binarize deep_data_types
        finitizable_data_types (desc as (card_assigns, _)) (ty, card) =
    let
      val deep = Util.member_type ty deep_data_types
      val co = MFH.is_codatatype ty
      val constructors =
        MFH.binarized_and_boxed_data_type_constrs context binarize ty
      val self_recs = map
        (is_self_recursive_constr_type o Term.type_of) constructors
      val num_self_recs = length (List.filter I self_recs)
      val num_non_self_recs = length self_recs - num_self_recs
      val self_rec = num_self_recs > 0
      fun is_complete facto = has_exact_card context facto
        finitizable_data_types card_assigns ty
      fun binder_types argument_ty =
        #1 (boolSyntax.strip_fun argument_ty)
      (* Concreteness asks whether each atom of the encoding denotes one
         definite value, not whether the encoding covers the whole type --
         that is [is_complete].  Only a function-typed constructor field can
         merge two different values into one atom, and only when its domain
         is inexactly represented, so a first-order field imposes no
         condition.  Demanding an exact cardinality of every field instead
         makes every recursive data type over an infinite type inconcrete,
         and [choose_reps_in_nut] then translates every positive equality on
         it to False: with [:num] capped, ``xs = [0]`` becomes unsatisfiable
         and its counterexample is lost. *)
      fun is_concrete facto =
        MFH.is_bitword_type ty orelse
        List.all (has_exact_card context facto finitizable_data_types
          card_assigns)
          (List.concat (map binder_types
            (List.concat
              (map MFH.constructor_arg_types constructors))))
      val complete = Util.pair_from_fun is_complete
      val concrete = Util.pair_from_fun is_concrete
      fun sum_dom_cards maximum =
        List.foldl (fn (constructor, total) =>
          total + domain_card maximum card_assigns constructor)
          0 constructors
      val paired = ListPair.zip (self_recs, constructors)
      val ordered =
        List.filter #1 paired @ List.filter (not o #1) paired
      val constrs = List.foldr (fn (entry, result) =>
        add_constr_spec desc (not co) card sum_dom_cards
          num_self_recs num_non_self_recs entry result) [] ordered
    in
      {typ = ty, card = card, co = co, self_rec = self_rec,
       complete = complete, concrete = concrete, deep = deep,
       constrs = constrs}
    end

  fun scope_from_descriptor context binarize deep_data_types
        finitizable_data_types (desc as (card_assigns, _)) =
    let
      val data_types = map
        (data_type_spec_from_scope_descriptor context binarize deep_data_types
          finitizable_data_types desc)
        (List.filter (MFH.is_data_type o #1) card_assigns)
      fun card ty = MFH.assignment_lookup card_assigns ty
      val bits =
        case card MFH.signed_bit_type of
            SOME signed => signed - 1
          | NONE => Option.getOpt (card MFH.unsigned_bit_type, 0)
    in
      {hol_ctxt = context, binarize = binarize,
       card_assigns = card_assigns, bits = bits,
       bisim_depth = Option.getOpt
         (Option.map (fn value => value - 1)
           (card MFH.bisim_iterator_type), ~1),
       data_types = data_types,
       ofs = offset_table_for_card_assigns data_types card_assigns}
    end

  (* Function and pair rows must be expanded for every analyzed type,
     including types classified as nonmonotonic. *)
  fun repair_cards_assigns_wrt_boxing_etc _ [] = []
    | repair_cards_assigns_wrt_boxing_etc mono_types
        ((SOME ty, candidates) :: assigns) =
      (if MFH.is_fun_type ty orelse MFH.is_pair_type ty then
         map (fn actual => (SOME actual, candidates))
           (List.filter (type_matches ty) mono_types)
       else
         [(SOME ty, candidates)]) @
      repair_cards_assigns_wrt_boxing_etc mono_types assigns
    | repair_cards_assigns_wrt_boxing_etc mono_types
        ((NONE, candidates) :: assigns) =
      (NONE, candidates) ::
      repair_cards_assigns_wrt_boxing_etc mono_types assigns

  fun take_at_most count values =
    let
      fun take 0 _ result = rev result
        | take _ [] result = rev result
        | take remaining (value :: rest) result =
            take (remaining - 1) rest (value :: result)
    in
      take (Int.max (0, count)) values []
    end

  fun same_max_assigns (left, right) =
    ListPair.allEq (fn ((left_const, left_max),
                        (right_const, right_max)) =>
      same_constructor left_const right_const andalso
      left_max = right_max) (left, right)

  fun same_description ((left_cards, left_maxes),
                        (right_cards, right_maxes)) =
    same_card_assigns (left_cards, right_cards) andalso
    same_max_assigns (left_maxes, right_maxes)

  fun description_compare ((left_cards, left_maxes),
        (right_cards, right_maxes)) =
    case strict_list_compare (pair_compare (Type.compare, Int.compare))
           (left_cards, right_cards) of
        EQUAL =>
          strict_list_compare (pair_compare (Term.compare, Int.compare))
            (left_maxes, right_maxes)
      | order => order

  fun distinct_descriptions values =
    List.rev (List.foldl (fn (value, result) =>
      if List.exists (fn other =>
           same_description (other, value)) result then result
      else value :: result) [] values)

  fun adaptive_card_type context ty =
    not (MFH.is_iterator_type ty) andalso not (MFH.is_bit_type ty) andalso
    (Type.is_vartype ty orelse not (MFH.is_finite_type context ty))

  fun adaptive_row context (Card ty, _) = adaptive_card_type context ty
    | adaptive_row _ (Max _, _) = false

  fun project_adaptive_row _ false column row = project_row column row
    | project_adaptive_row context true column
        (row as (kind, candidates)) =
        if adaptive_row context row then (kind, [column + 1])
        else project_row column (kind, candidates)

  fun project_adaptive_block context iterative (column, block) =
    map (project_adaptive_row context iterative column) block

  type scope_cursor =
    {context : context,
     binarize : bool,
     blocks : block list,
     iterative : bool,
     combinations : combination_cursor,
     deep_data_types : hol_type list,
     finitizable_data_types : hol_type list,
     emitted : (scope_desc, unit) Redblackmap.dict ref,
     skipped : int ref}

  fun new_scope_cursor context binarize iterative cards_assigns maxes_assigns
        iters_assigns bitss bisim_depths mono_types nonmono_types
        deep_data_types finitizable_data_types =
    let
      val cards_assigns = repair_cards_assigns_wrt_boxing_etc
        (mono_types @ nonmono_types) cards_assigns
      val blocks = blocks_for_types context binarize cards_assigns
        maxes_assigns iters_assigns bitss bisim_depths mono_types
        nonmono_types
      fun block_rank block =
        if iterative andalso List.exists (adaptive_row context) block then NONE
        else SOME (rank_of_block block)
    in
      {context = context, binarize = binarize, blocks = blocks,
       iterative = iterative,
       combinations = new_combination_cursor (map block_rank blocks),
       deep_data_types = deep_data_types,
       finitizable_data_types = finitizable_data_types,
       emitted = ref (Redblackmap.mkDict description_compare),
       skipped = ref 0}
    end

  fun scope_cursor_batch_with_stop (cursor : scope_cursor) count stop =
    let
      val before_skipped = !(#skipped cursor)
      fun next remaining scopes =
        if stop () then (rev scopes, false, true)
        else if remaining <= 0 then (rev scopes, false, false)
        else
          case combination_cursor_next (#combinations cursor) of
              NONE => (rev scopes, true, false)
            | SOME columns =>
                let
                  val rows = List.concat
                    (ListPair.map
                      (project_adaptive_block (#context cursor)
                        (#iterative cursor))
                      (columns, #blocks cursor))
                  val descriptor = scope_descriptor_from_block rows
                  val repaired = Option.map (fn cards =>
                    (map (repair_iterator_assign (#context cursor) cards)
                       cards, #2 descriptor))
                    (repair_card_assigns (#context cursor)
                      (#binarize cursor) descriptor)
                in
                  case repaired of
                      NONE =>
                        (#skipped cursor := !(#skipped cursor) + 1;
                         next remaining scopes)
                    | SOME description =>
                        if Option.isSome (Redblackmap.peek
                             (!(#emitted cursor), description)) then
                          (#skipped cursor := !(#skipped cursor) + 1;
                           next remaining scopes)
                        else
                          let
                            val scope = scope_from_descriptor (#context cursor)
                              (#binarize cursor) (#deep_data_types cursor)
                              (#finitizable_data_types cursor) description
                            val _ = #emitted cursor := Redblackmap.insert
                              (!(#emitted cursor), description, ())
                          in
                            next (remaining - 1) (scope :: scopes)
                          end
                end
      val (scopes, done, stopped) = next (Int.max (0, count)) []
    in
      {scopes = scopes, done = done,
       stopped = stopped,
       skipped = !(#skipped cursor) - before_skipped}
    end

  fun all_scopes context binarize cards_assigns maxes_assigns
        iters_assigns bitss bisim_depths mono_types nonmono_types
        deep_data_types finitizable_data_types =
    let
      val cards_assigns =
        repair_cards_assigns_wrt_boxing_etc
          (mono_types @ nonmono_types) cards_assigns
      val blocks = blocks_for_types context binarize cards_assigns
        maxes_assigns iters_assigns bitss bisim_depths mono_types
        nonmono_types
      val ranks = map rank_of_block blocks
      val combination_ranks = map (fn rank => (rank, 0)) ranks
      val selected = all_combinations_ordered_smartly_at_most max_scopes
        combination_ranks
      (* A selected combination can be invalid (notably a disabled
         bisimulation depth maps to a zero-cardinality iterator).  Omitting it
         is not an exhaustive check, so include it in the skipped count. *)
      val selected_descriptions = List.mapPartial
        (scope_descriptor_from_combination context binarize blocks) selected
      val descriptions =
        if length selected_descriptions <= distinct_threshold then
          distinct_descriptions selected_descriptions
        else selected_descriptions
    in
      (saturated_int (number_of_combinations combination_ranks -
         IntInf.fromInt (length selected_descriptions)),
       map (scope_from_descriptor context binarize deep_data_types
         finitizable_data_types) descriptions)
    end

  fun is_number_type ty =
    is_asymmetric_non_data_type ty orelse
    Option.isSome (MFH.numeric_type_card ty) orelse
    Option.isSome (MFH.word_dimension ty) orelse
    MFH.is_char_type ty

  fun is_type_fundamentally_monotonic ty =
    (MFH.is_data_type ty andalso not (MFH.is_quot_type ty) andalso
     (not (MFH.is_typedef ty) orelse MFH.is_univ_typedef ty)) orelse
    is_number_type ty

  fun mono_override monos ty =
    Util.triple_lookup (fn (actual, pattern) =>
      type_matches pattern actual) monos ty

  fun is_type_monotonic_with actually_monotonic monos ty =
    case mono_override monos ty of
        SOME (SOME value) => value
      | _ => is_type_fundamentally_monotonic ty orelse
             actually_monotonic ty

  fun mono_partition_with actually_monotonic monos types =
    List.partition
      (is_type_monotonic_with actually_monotonic monos) types
end

