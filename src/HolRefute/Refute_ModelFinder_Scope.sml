structure Refute_ModelFinder_Scope = struct
  open Portable Feedback
  infix |>

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

  val default_cards = List.tabulate (10, fn index => index + 1)
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

  fun constructor_result_type constructor =
    #2 (boolSyntax.strip_fun (Term.type_of constructor))

  fun same_constructor left right =
    MFH.constructor_name left = MFH.constructor_name right andalso
    Util.same_type (constructor_result_type left)
      (constructor_result_type right)

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
          else if MFH.is_iterator_type ty orelse
                  MFH.is_integer_type ty orelse MFH.is_bit_type ty orelse
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

  fun scope_less_eq (left : scope) (right : scope) =
    ListPair.allEq (op <=)
      (map #2 (#card_assigns left), map #2 (#card_assigns right))

  fun rank_of_row (_, candidates) = length candidates

  fun rank_of_block block =
    List.foldl Int.max 1 (map rank_of_row block)

  fun project_row _ (kind, []) = (kind, [1]) (* desperate measure *)
    | project_row column (kind, candidates) =
      (kind, [List.nth (candidates,
        Int.min (column, length candidates - 1))])

  fun project_block (column, block) = map (project_row column) block

  fun lookup_ints_assign equal assigns key =
    case Util.triple_lookup equal assigns key of
        SOME candidates => candidates
      | NONE => raise err "lookup_ints_assign" "missing assignment"

  fun lookup_type_ints_assign assigns ty =
    map (fn value => Int.max (1, value))
      (lookup_ints_assign (fn (actual, pattern) =>
         type_matches pattern actual) assigns ty)

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

  fun lookup_iter_ints_assign assigns predicate =
    lookup_group_iter_ints_assign assigns [predicate]

  fun row_for_constr maxes_assigns constructor =
    SOME (Max constructor,
      lookup_const_ints_assign maxes_assigns constructor)
    handle HOL_ERR _ => NONE

  fun bit_card bits = Int.min (max_bits, Int.max (1, bits))

  fun block_for_type context binarize cards_assigns maxes_assigns
        iters_assigns bitss bisim_depths ty =
    if MFH.is_bisim_iterator_type ty then
      [(Card ty, map (fn depth => Int.max (0, depth) + 1)
        bisim_depths)]
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

  fun all_combinations_ordered_smartly ranks =
    Util.all_combinations ranks
    |> map (fn combination =>
         (combination_cost combination, combination))
    |> Lib.sort (fn (left, _) => fn (right, _) => left <= right)
    |> map #2

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

  fun constructor_domain_card maximum card_assigns constructor =
    List.foldl (fn (argument_ty, total) =>
      let
        val card = MFH.bounded_card_of_type maximum ~1
          card_assigns argument_ty
      in
        if total = 0 orelse card = 0 then 0
        else if total >= maximum orelse card >= maximum orelse
                total > maximum div card then maximum
        else total * card
      end) 1 (MFH.constructor_arg_types constructor)

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

  fun domain_card maximum card_assigns constructor =
    List.foldl (fn (argument_ty, total) =>
      let
        val card = MFH.bounded_card_of_type maximum maximum
          card_assigns argument_ty
      in
        if total = 0 orelse card = 0 then 0
        else if total >= maximum orelse card >= maximum orelse
                total > maximum div card then maximum
        else total * card
      end) 1 (MFH.constructor_arg_types constructor)

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

  fun has_exact_card context facto finitizable_data_types
        card_assigns ty =
    let val card = MFH.card_of_type card_assigns ty
    in
      card = MFH.bounded_exact_card_of_type context
        (if facto then finitizable_data_types else [])
        (card + 1) 0 card_assigns ty
    end

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
      fun is_concrete facto =
        MFH.is_bitword_type ty orelse
        (* FIXME: looks wrong; other types than just functions might be
           abstract. "is_complete" is also suspicious. *)
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

  fun distinct_descriptions values =
    List.rev (List.foldl (fn (value, result) =>
      if List.exists (fn other =>
           same_description (other, value)) result then result
      else value :: result) [] values)

  fun all_scopes context binarize cards_assigns maxes_assigns
        iters_assigns bitss bisim_depths mono_types nonmono_types deep_data_types
        finitizable_data_types =
    let
      val cards_assigns =
        repair_cards_assigns_wrt_boxing_etc
          (mono_types @ nonmono_types) cards_assigns
      val blocks = blocks_for_types context binarize cards_assigns
        maxes_assigns iters_assigns bitss bisim_depths mono_types
        nonmono_types
      val ranks = map rank_of_block blocks
      val all = all_combinations_ordered_smartly
        (map (fn rank => (rank, 0)) ranks)
      val selected = take_at_most max_scopes all
      val descriptions = List.mapPartial
        (scope_descriptor_from_combination context binarize blocks) selected
      val descriptions =
        if length descriptions <= distinct_threshold then
          distinct_descriptions descriptions
        else descriptions
    in
      (length all - length selected,
       map (scope_from_descriptor context binarize deep_data_types
         finitizable_data_types) descriptions)
    end

  fun is_number_type ty =
    MFH.is_iterator_type ty orelse MFH.is_integer_type ty orelse
    MFH.is_bit_type ty orelse
    Option.isSome (MFH.numeric_type_card ty) orelse
    Option.isSome (MFH.word_dimension ty)

  fun is_type_fundamentally_monotonic ty =
    (MFH.is_data_type ty andalso not (MFH.is_quot_type ty)) orelse
    is_number_type ty

  (* M3 has no monotonicity calculus.  Returning false is exactly
     Isabelle's timeout path at nitpick.ML:363 and is always sound. *)
  fun is_type_actually_monotonic _ = false

  fun mono_override monos ty =
    Util.triple_lookup (fn (actual, pattern) =>
      type_matches pattern actual) monos ty

  fun is_type_monotonic_with actually_monotonic monos ty =
    case mono_override monos ty of
        SOME (SOME value) => value
      | _ => is_type_fundamentally_monotonic ty orelse
             actually_monotonic ty

  fun is_type_monotonic monos ty =
    is_type_monotonic_with is_type_actually_monotonic monos ty

  fun mono_partition_with actually_monotonic monos types =
    List.partition
      (is_type_monotonic_with actually_monotonic monos) types

  fun mono_partition monos types =
    mono_partition_with is_type_actually_monotonic monos types
end
