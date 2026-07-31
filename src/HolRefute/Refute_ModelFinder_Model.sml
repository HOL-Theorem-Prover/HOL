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

  type term_postprocessor = term -> term
  type term_postprocessor_snapshot
  val register_term_postprocessor :
    hol_type -> term_postprocessor -> unit
  val lookup_term_postprocessor :
    hol_type -> term_postprocessor option
  val snapshot_term_postprocessors : unit -> term_postprocessor_snapshot
  val restore_term_postprocessors : term_postprocessor_snapshot -> unit
  val postprocess_term : term_postprocessor_snapshot -> term -> term
  val register_frac_type_rat : unit -> unit

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

  val format_type : int list -> int list -> hol_type -> hol_type
  val format_term_type :
    Refute_ModelFinder_HOL.mf_context ->
    (term option * int list) list -> term -> hol_type
  val format_fun : hol_type -> term -> term

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

  val reconstruct_formatted :
    {context : Refute_ModelFinder_HOL.mf_context,
     formats : (term option * int list) list,
     scope : scope,
     atoms : (hol_type option * string list) list,
     special_funs : Refute_ModelFinder_HOL.special_fun list,
     real_frees : term list,
     eval_terms : term list,
     free_names : nut list,
     sel_names : nut list,
     nonsel_names : nut list,
     rel_table : nut Refute_ModelFinder_Nut.NameTable.table,
     bounds : raw_bound list} -> reconstruction

  val reconstruct_both :
    {context : Refute_ModelFinder_HOL.mf_context,
     formats : (term option * int list) list,
     scope : scope,
     atoms : (hol_type option * string list) list,
     special_funs : Refute_ModelFinder_HOL.special_fun list,
     real_frees : term list,
     eval_terms : term list,
     free_names : nut list,
     sel_names : nut list,
     nonsel_names : nut list,
     rel_table : nut Refute_ModelFinder_Nut.NameTable.table,
     bounds : raw_bound list} ->
    {raw : reconstruction,
     displayed : reconstruction,
     postprocessors : term_postprocessor_snapshot}

  val model_report : reconstruction -> Refute_Core.model_report
  val display_counterexample :
    term_postprocessor_snapshot -> reconstruction ->
    Refute_Core.counterexample -> Refute_Core.counterexample
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
structure Util = Refute_ModelFinder_Util

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

type term_postprocessor = term -> term

type term_postprocessor_entry =
  {pattern : hol_type, postprocessor : term_postprocessor, serial : int}
type term_postprocessor_snapshot =
  {entries : term_postprocessor_entry list, next_serial : int}

(* Model display extensions are process-local ML data.  The registry uses
   type patterns: every pattern that matches an actual type participates.
   Composition is deterministic: general patterns run before strictly more
   specific patterns, and otherwise older registrations run before newer
   ones.  Re-registering an alpha-equivalent pattern replaces its callback
   without adding a duplicate or changing its established position. *)
val term_postprocessors = ref
  ({entries = [], next_serial = 0} : term_postprocessor_snapshot)

fun with_term_postprocessor_lock body = MFH.with_registration_lock body

fun snapshot_term_postprocessors () =
  with_term_postprocessor_lock (fn () => !term_postprocessors)

fun restore_term_postprocessors snapshot =
  with_term_postprocessor_lock (fn () => term_postprocessors := snapshot)

fun pattern_matches pattern actual =
  Lib.can (Type.match_type pattern) actual

fun same_pattern left right =
  pattern_matches left right andalso pattern_matches right left

fun strictly_more_general left right =
  pattern_matches left right andalso not (pattern_matches right left)

fun matching_postprocessors
      ({entries, ...} : term_postprocessor_snapshot) actual =
  let
    val matches = List.filter (fn {pattern, ...} =>
      pattern_matches pattern actual) entries
    fun generality ({pattern, ...} : term_postprocessor_entry) =
      length (List.filter (fn {pattern = other, ...} =>
        strictly_more_general other pattern) matches)
    fun key (entry : term_postprocessor_entry) =
      (generality entry, #serial entry, #postprocessor entry)
    fun compare ((left_generality, left_serial, _),
          (right_generality, right_serial, _)) =
      case Int.compare (left_generality, right_generality) of
          EQUAL => Int.compare (left_serial, right_serial)
        | order => order
  in
    map #3 (Listsort.sort compare (map key matches))
  end

fun safe_postprocess postprocessor candidate =
  let val processed = postprocessor candidate in
    if Util.same_type (Term.type_of processed) (Term.type_of candidate) then
      processed
    else
      candidate
  end
  handle error =>
    if Exn.is_interrupt error then Exn.reraise error else candidate

fun composed_postprocessor snapshot ty =
  case matching_postprocessors snapshot ty of
      [] => NONE
    | postprocessors => SOME (fn term =>
        List.foldl (fn (postprocessor, candidate) =>
          safe_postprocess postprocessor candidate) term postprocessors)

fun lookup_term_postprocessor ty =
  composed_postprocessor (snapshot_term_postprocessors ()) ty

fun insert_postprocessor pattern postprocessor
      ({entries, next_serial} : term_postprocessor_snapshot) =
  let
    fun replace [] =
          ([{pattern = pattern, postprocessor = postprocessor,
             serial = next_serial}], next_serial + 1)
      | replace ((entry as {pattern = old, serial, ...}) :: rest) =
          if same_pattern old pattern then
            ({pattern = pattern, postprocessor = postprocessor,
              serial = serial} :: rest, next_serial)
          else
            let val (tail, next) = replace rest
            in (entry :: tail, next) end
    val (entries, next_serial) = replace entries
  in
    {entries = entries, next_serial = next_serial}
  end

fun register_term_postprocessor pattern postprocessor =
  with_term_postprocessor_lock (fn () =>
    term_postprocessors :=
      insert_postprocessor pattern postprocessor (!term_postprocessors))

fun postprocess_term snapshot term =
  let
    fun apply candidate =
      case composed_postprocessor snapshot (Term.type_of candidate) of
          SOME postprocessor => postprocessor candidate
        | NONE => candidate
    fun descend candidate =
      apply
        (if Term.is_abs candidate then
           let val (variable, body) = Term.dest_abs candidate
           in Term.mk_abs (variable, descend body) end
         else
           case Lib.total Term.dest_comb candidate of
               SOME (function, argument) =>
                 Term.mk_comb (descend function, descend argument)
             | NONE => candidate)
  in
    if null (#entries snapshot) then term else descend term
  end

(* [raw_constructor_name] deliberately covers reconstructed variables as well
   as constants: the atom reaching this postprocessor is usually a variable
   whose stripped name is the mangled constant, so a [dest_thy_const] test
   here would silently stop matching. *)
fun frac_atom_to_rat term =
  case HolKernel.strip_comb term of
      (constructor, [pair]) =>
        if MFH.raw_constructor_name constructor = "frac$abs_frac" then
          let
            val (numerator, denominator) = pairSyntax.dest_pair pair
            val rat_cons = Term.prim_mk_const
              {Thy = "rat", Name = "rat_cons"}
          in
            if Util.same_type (Term.type_of numerator) MFH.int_type andalso
               Util.same_type (Term.type_of denominator) MFH.int_type then
              let
                val denominator =
                  if Arbint.compare
                       (intSyntax.int_of_term numerator, Arbint.zero) = EQUAL
                  then intSyntax.term_of_int Arbint.one
                  else denominator
              in
                Term.list_mk_comb (rat_cons, [numerator, denominator])
              end
            else
              term
          end handle HOL_ERR _ => term
        else
          term
    | _ => term

fun prepare_rat_term_postprocessor () =
  let
    val pattern = Type.mk_thy_type
      {Thy = "rat", Tyop = "rat", Args = []}
    val updated = insert_postprocessor pattern frac_atom_to_rat
      (!term_postprocessors)
  in
    fn () => term_postprocessors := updated
  end

fun register_frac_type_rat () =
  with_term_postprocessor_lock (fn () =>
    let
      (* Frac validation and all list construction happen before either
         registry is changed.  Both following commits are callback-free and
         execute while all term/Frac registrations share the same mutex. *)
      val commit_frac =
        MFH.prepare_frac_type_unlocked MFH.rat_frac_registration
      val commit_postprocessor = prepare_rat_term_postprocessor ()
    in
      Thread_Attributes.uninterruptible (fn _ => fn () =>
        (commit_frac ();
         commit_postprocessor ())) ()
    end)

(* Per-type running counters plus the numbers already handed out, so
   that numbering an atom is a pair of lookups rather than a scan. *)
type atom_pool =
  {counts : (hol_type, int) Redblackmap.dict,
   numbers : (hol_type * int, int) Redblackmap.dict,
   terms : (hol_type * int, term) Redblackmap.dict,
   used : (hol_type, term list) Redblackmap.dict} ref

fun new_atom_pool () : atom_pool =
  ref {counts = Redblackmap.mkDict Type.compare,
       numbers = Redblackmap.mkDict
         (Portable.pair_compare (Type.compare, Int.compare)),
       terms = Redblackmap.mkDict
         (Portable.pair_compare (Type.compare, Int.compare)),
       used = Redblackmap.mkDict Type.compare}

type context =
  {scope : scope,
   atoms : (hol_type option * string list) list,
   sel_names : nut list,
   rel_table : nut MFNT.NameTable.table,
   bounds : raw_bound list,
   atom_avoids : term list,
   pool : atom_pool}

fun err function message =
  Feedback.mk_HOL_ERR "Refute_ModelFinder_Model" function message

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
  let
    fun exact (SOME pattern_ty, _) = Util.same_type pattern_ty ty
      | exact _ = false
    fun matches (SOME pattern_ty, _) =
          Lib.can (Type.match_type pattern_ty) ty
      | matches _ = false
    fun fallback (pattern, _) = not (Option.isSome pattern)
  in
    case List.find exact atoms of
        SOME (_, names) => names
      | NONE =>
          (case List.find matches atoms of
               SOME (_, names) => names
             | NONE =>
                 (case List.find fallback atoms of
                      SOME (_, names) => names
                    | NONE => []))
  end

fun atom_number (pool : atom_pool) ty atom =
  let val {counts, numbers, terms, used} = !pool in
    case Redblackmap.peek (numbers, (ty, atom)) of
        SOME number => number
      | NONE =>
          let
            val number = 1 + Option.getOpt (Redblackmap.peek (counts, ty), 0)
            val _ = pool :=
              {counts = Redblackmap.insert (counts, ty, number),
               numbers = Redblackmap.insert (numbers, (ty, atom), number),
               terms = terms, used = used}
          in
            number
          end
  end

fun atom_term ({atoms, atom_avoids, pool, ...} : context) ty atom =
  let
    val number = atom_number pool ty atom
    val {terms, used, ...} = !pool
    val key = (ty, number)
    val overrides = type_atom_names atoms ty
    val requested =
      if number <= length overrides then
        Term.mk_var (List.nth (overrides, number - 1), ty)
      else
        MFN.fake_atom number ty
  in
    case Redblackmap.peek (terms, key) of
        SOME assigned => assigned
      | NONE =>
          let
            (* Names in [upd_atoms] are preferences, not identities.  A
               per-type freshening cache makes every solver atom distinct,
               including duplicate overrides and fallback-name collisions. *)
            val avoids = Term.mk_var ("?", ty) :: atom_avoids @
              Option.getOpt (Redblackmap.peek (used, ty), [])
            val assigned = Term.variant avoids requested
            val _ = pool :=
              {counts = #counts (!pool), numbers = #numbers (!pool),
               terms = Redblackmap.insert (terms, key, assigned),
               used = Redblackmap.insert
                 (used, ty, assigned :: Option.getOpt
                   (Redblackmap.peek (used, ty), []))}
          in
            assigned
          end
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
    val has_unknown = List.exists
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
    (* An exact set asserts every omitted member is absent.  Retaining the
       true tuples while discarding unknown memberships would therefore make
       a solver partiality look like a negative fact. *)
    if has_unknown then
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
                  val power = Util.reasonable_power 2 index
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
              val chunks = Util.chunk_list width tuple
              val domains = List.tabulate (card, fn atom =>
                MFH.unarize_unbox_etc_term
                  (term_for_atom seen domain_ty atom card))
              val ranges = map (fn chunk =>
                MFH.unarize_unbox_etc_term
                  (term_for_rep true seen range_ty range_rep [chunk])) chunks
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
                MFH.unarize_unbox_etc_term
                  (term_for_rep true seen domain_ty domain_rep [tuple]))
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
                MFH.unarize_unbox_etc_term
                  (term_for_rep false seen domain_ty domain_rep [tuple]))
                combinations
              val ranges = map (fn tuple =>
                MFH.unarize_unbox_etc_term
                  (term_for_rep false seen range_ty range_rep
                    (tails tuple)))
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
              val tuple = Util.nth_combination
                (Util.replicate_list domain_card [(range_card, 0)]) atom
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
            else if Util.same_type ty MFH.num_type then
              numSyntax.term_of_int atom
            else if Util.same_type ty MFH.int_type then
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
            Util.same_type (#1 (Type.dom_rng (MFNT.type_of name))) ty)
            sel_names
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
     rel_table = rel_table, bounds = bounds, atom_avoids = [],
     pool = new_atom_pool ()}
    maybe_opt ty representation tuples

fun same_free name ty term =
  case Lib.total Term.dest_var term of
      SOME (other, other_ty) => name = other andalso Util.same_type ty other_ty
    | NONE => false

fun free_name_for_term free_names term =
  let val (name, ty) = Term.dest_var term
  in
    case List.find (fn candidate =>
           case candidate of
               MFNT.FreeName (other, other_ty, _) =>
                 name = other andalso
                 Util.same_type (MFH.unarize_unbox_etc_type ty)
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
                  fixed_indices)) (Util.index_seq 0 (maximum + 1))
              val missing_vars = ListPair.map (fn (index, argument_ty) =>
                Term.mk_var ("arg" ^ Int.toString (index + 1), argument_ty))
                (missing_indices,
                 Util.filter_indices missing_indices argument_types)
              fun argument index =
                case List.find (fn (fixed, _) => fixed = index)
                       (ListPair.zip (fixed_indices, fixed_terms)) of
                    SOME (_, fixed) => friendly_term fixed
                  | NONE =>
                      List.nth (missing_vars,
                        Lib.index (fn missing => missing = index)
                          missing_indices)
              val arguments = map argument
                (Util.index_seq 0 (maximum + 1))
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

fun positive_format format = List.filter (fn count => count > 0) format

fun last_and_front values =
  case rev values of
      last :: rest => (rev rest, last)
    | [] => raise err "last_and_front" "empty format"

fun intersect_formats _ [] = []
  | intersect_formats [] _ = []
  | intersect_formats left right =
      let
        val (left_front, left_last) = last_and_front left
        val (right_front, right_last) = last_and_front right
        val next_left = left_front @
          (if left_last > right_last then [left_last - right_last] else [])
        val next_right = right_front @
          (if right_last > left_last then [right_last - left_last] else [])
      in
        intersect_formats next_left next_right @
        [Int.min (left_last, right_last)]
      end

fun format_type default_format requested ty =
  let
    val ty = MFH.uniterize_unarize_unbox_etc_type ty
    val requested = positive_format requested
  in
    if List.all (fn count => count = 1) requested then ty
    else
      let
        val (argument_tys, result_ty) = boolSyntax.strip_fun ty
        val formatted_arguments = map
          (format_type default_format default_format) argument_tys
        val reverse_groups = Util.chunk_list_unevenly (rev requested)
          (rev formatted_arguments)
        val grouped = rev
          (map (pairSyntax.list_mk_prod o rev) reverse_groups)
      in
        boolSyntax.list_mk_fun (grouped, result_ty)
      end
  end

fun format_term_matches pattern actual =
  case (Lib.total Term.dest_thy_const pattern,
        Lib.total Term.dest_thy_const actual) of
      (SOME {Thy = pattern_thy, Name = pattern_name, ...},
       SOME {Thy = actual_thy, Name = actual_name, ...}) =>
        pattern_thy = actual_thy andalso pattern_name = actual_name andalso
        MFH.type_matches_unboxed
          (Term.type_of pattern, Term.type_of actual)
    | _ =>
        (case (Lib.total Term.dest_var pattern,
               Lib.total Term.dest_var actual) of
             (SOME (pattern_name, pattern_ty),
              SOME (actual_name, actual_ty)) =>
               pattern_name = actual_name andalso
               MFH.type_matches_unboxed (pattern_ty, actual_ty)
           | _ => Term.aconv pattern actual)

fun binder_count ty = length (#1 (boolSyntax.strip_fun
  (MFH.uniterize_unarize_unbox_etc_type ty)))

fun abstraction_count term =
  if Term.is_abs term then 1 + abstraction_count (Term.body term) else 0

fun skolem_arity name =
  if MFN.is_skolem_name name then
    let
      val (_, layer) = Substring.position MFN.skolem_prefix
        (Substring.full name)
    in
      if Substring.isEmpty layer then NONE
      else
        let
          val suffix = Substring.triml (size MFN.skolem_prefix) layer
          val (arity, _) = Substring.position "@" suffix
        in
          Int.fromString (Substring.string arity)
        end
    end
  else
    NONE

fun const_format context term =
  let
    val count = binder_count (Term.type_of term)
    val generated_name = Option.map #1 (Lib.total Term.dest_var term)
  in
    case generated_name of
        SOME name =>
          if MFN.is_unrolled_name name then
            let
              val (_, predicate_ty) = Type.dom_rng (Term.type_of term)
              val original = user_friendly_const []
                (MFN.original_name name) predicate_ty
            in
              const_format context original
            end
          else
            (case skolem_arity name of
                 SOME fixed =>
                   [Int.min (fixed, count), Int.max (0, count - fixed)]
               | NONE => [count])
      | NONE =>
          if Term.is_const term then
            case MFH.def_of_const context term of
                SOME rhs =>
                  if MFH.raw_fixpoint_kind term <> MFH.NoFp orelse
                     MFH.fixpoint_kind_of_rhs rhs <> MFH.NoFp then
                    let val fixed =
                      Int.min (count, abstraction_count rhs)
                    in [fixed, count - fixed] end
                  else [count]
              | NONE => [count]
          else
            [count]
  end

fun default_format formats =
  case List.find (fn (key, _) => not (Option.isSome key)) formats of
      SOME (_, format) => format
    | NONE => [1]

fun lookup_format context formats term =
  case List.find (fn (key, _) =>
         case key of
             SOME pattern => format_term_matches pattern term
           | NONE => false) formats of
      SOME (_, format) => format
    | NONE =>
        let
          val generated =
            case Lib.total Term.dest_var term of
                SOME (name, _) => MFN.is_reserved_name name
              | NONE => false
        in
          if Term.is_const term orelse generated then
            intersect_formats (default_format formats)
              (const_format context term)
          else
            default_format formats
        end

fun format_term_type context formats term =
  format_type (default_format formats) (lookup_format context formats term)
    (Term.type_of term)

fun format_metadata_name name =
  case uncurry_info name of
      SOME (_, _, original) => format_metadata_name original
    | NONE => name

fun repair_special_format fixed_indices count format =
  let
    val indices = rev (Util.index_seq 0 count)
    val chunks = Util.chunk_list_unevenly (rev (positive_format format))
      indices
    fun retained chunk = List.filter (fn index =>
      not (List.exists (fn fixed => fixed = index) fixed_indices)) chunk
  in
    rev (map length (List.filter (not o null) (map retained chunks)))
  end

fun special_format context formats special_funs name =
  let
    fun generated_name (_, generated) =
      case Lib.total Term.dest_var generated of
          SOME (candidate, _) => candidate = name
        | NONE => false
  in
    Option.map (fn ((original, fixed_indices, _), _) =>
      let
        val original_count = binder_count (Term.type_of original)
      in
        case List.find (fn (key, _) =>
               case key of
                   SOME pattern => format_term_matches pattern original
                 | NONE => false) formats of
            SOME (_, requested) =>
              repair_special_format fixed_indices original_count requested
          | NONE => intersect_formats (default_format formats)
              (repair_special_format fixed_indices original_count
                (const_format context original))
      end) (List.find generated_name special_funs)
  end

fun format_term_type_for_name context formats special_funs name term =
  let val metadata_name = format_metadata_name name in
  case special_format context formats special_funs metadata_name of
      SOME format =>
        format_type (default_format formats) format (Term.type_of term)
    | NONE =>
        if MFN.is_unrolled_name metadata_name then
          let
            val (_, predicate_ty) = Type.dom_rng (Term.type_of term)
            val predicate = user_friendly_const special_funs
              (MFN.original_name metadata_name) predicate_ty
          in
            format_type (default_format formats)
              (lookup_format context formats predicate) (Term.type_of term)
          end
        else
          case skolem_arity metadata_name of
              SOME fixed =>
                let val count = binder_count (Term.type_of term)
                in
                  format_type (default_format formats)
                    (intersect_formats (default_format formats)
                      [Int.min (fixed, count),
                       Int.max (0, count - fixed)])
                    (Term.type_of term)
                end
            | NONE =>
                (case List.find (fn (key, _) =>
                         case key of
                             SOME pattern =>
                               format_term_matches pattern term
                           | NONE => false) formats of
                     SOME (_, format) =>
                       format_type (default_format formats) format
                         (Term.type_of term)
                   | NONE => format_term_type context formats term)
  end

fun pair_leaves ty =
  if MFH.is_pair_type ty then
    let val (left, right) = pairSyntax.dest_prod ty
    in pair_leaves left @ pair_leaves right end
  else
    [ty]

fun flatten_pair_term ty term =
  if MFH.is_pair_type ty then
    let
      val (left_ty, right_ty) = pairSyntax.dest_prod ty
      (* A decoded value can have pair type without being a literal pair.
         Selectors preserve the value while making its leaves explicit. *)
      val (left, right) =
        case Lib.total pairSyntax.dest_pair term of
            SOME pair => pair
          | NONE =>
              (pairSyntax.mk_fst term, pairSyntax.mk_snd term)
    in
      flatten_pair_term left_ty left @ flatten_pair_term right_ty right
    end
  else
    [term]

fun build_pair_term ty terms =
  if MFH.is_pair_type ty then
    let
      val (left_ty, right_ty) = pairSyntax.dest_prod ty
      val (left, terms) = build_pair_term left_ty terms
      val (right, terms) = build_pair_term right_ty terms
    in
      (pairSyntax.mk_pair (left, right), terms)
    end
  else
    case terms of
        term :: rest =>
          if Util.same_type ty (Term.type_of term) then (term, rest)
          else raise err "build_pair_term" "tuple leaf type mismatch"
      | [] => raise err "build_pair_term" "not enough tuple leaves"

fun reshape_pair target_ty source_ty term =
  let
    val source_leaves = pair_leaves source_ty
    val target_leaves = pair_leaves target_ty
    val _ = if Lib.list_eq Util.same_type source_leaves target_leaves then ()
      else raise err "reshape_pair" "tuple types have different leaves"
    val (result, rest) = build_pair_term target_ty
      (flatten_pair_term source_ty term)
  in
    if null rest then result
    else raise err "reshape_pair" "unused tuple leaves"
  end

fun marker_with_type ty marker =
  case Lib.total Term.dest_var marker of
      SOME (name, _) => Term.mk_var (name, ty)
    | NONE =>
        if Util.same_type ty (Term.type_of marker) then marker
        else raise err "marker_with_type" "cannot retype function base"

fun dest_display_fun term =
  case Lib.total combinSyntax.dest_update_comb term of
      SOME ((point, value), base) =>
        let val (marker, pairs) = dest_display_fun base
        in (marker, pairs @ [(point, value)]) end
    | NONE =>
        if combinSyntax.is_K_1 term then
          (combinSyntax.dest_K_1 term, [])
        else
          raise err "dest_display_fun" "not a reconstructed function"

fun make_display_fun domain_ty marker pairs =
  List.foldl (fn (pair, base) => make_update pair base)
    (combinSyntax.mk_K_1 (marker, domain_ty)) pairs

fun dest_literal_set term =
  if pred_setSyntax.is_empty term then SOME []
  else
    case Lib.total pred_setSyntax.dest_insert term of
        SOME (element, rest) =>
          Option.map (fn elements => element :: elements)
            (dest_literal_set rest)
      | NONE => NONE

fun make_literal_set element_ty elements =
  List.foldr (fn (element, set) =>
      pred_setSyntax.mk_insert (element, set))
    (pred_setSyntax.mk_empty element_ty) elements

fun factor_count ty =
  if MFH.is_pair_type ty then
    let val (left, right) = pairSyntax.dest_prod ty
    in factor_count left + factor_count right end
  else 1

fun factor_out_types left right =
  if MFH.is_pair_type left andalso MFH.is_pair_type right then
    let
      val (left_head, left_tail) = pairSyntax.dest_prod left
      val (right_head, right_tail) = pairSyntax.dest_prod right
      val left_count = factor_count left_head
      val right_count = factor_count right_head
    in
      if left_count = right_count then
        let
          val ((left_prefix, left_rest),
               (right_prefix, right_rest)) =
            factor_out_types left_tail right_tail
        in
          ((pairSyntax.mk_prod (left_head, left_prefix), left_rest),
           (pairSyntax.mk_prod (right_head, right_prefix), right_rest))
        end
      else if left_count < right_count then
        (case factor_out_types left right_head of
             (left_parts, (right_prefix, NONE)) =>
               (left_parts, (right_prefix, SOME right_tail))
           | (left_parts, (right_prefix, SOME right_rest)) =>
               (left_parts,
                (right_prefix,
                 SOME (pairSyntax.mk_prod (right_rest, right_tail)))))
      else
        let val (right_parts, left_parts) =
          factor_out_types right left
        in (left_parts, right_parts) end
    end
  else if MFH.is_pair_type left then
    let val (first, second) = pairSyntax.dest_prod left
    in ((first, SOME second), (right, NONE)) end
  else if MFH.is_pair_type right then
    let val (first, second) = pairSyntax.dest_prod right
    in ((left, NONE), (first, SOME second)) end
  else
    ((left, NONE), (right, NONE))

fun format_fun target_ty term =
  let
    fun deepest_marker target candidate =
      case Lib.total dest_display_fun candidate of
          SOME (marker, _) =>
            if MFH.is_fun_type (Term.type_of marker) then
              deepest_marker target marker
            else marker_with_type target marker
        | NONE => marker_with_type target candidate

    fun split_point source_ty left_ty right_ty point =
      let
        val leaves = flatten_pair_term source_ty point
        val (left, leaves) = build_pair_term left_ty leaves
        val (right, leaves) = build_pair_term right_ty leaves
      in
        if null leaves then (left, right)
        else raise err "format_fun" "unused curried tuple leaves"
      end

    fun add_group ((left, right, value), []) =
          [(left, [(right, value)])]
      | add_group ((left, right, value), (key, pairs) :: rest) =
          if Term.aconv left key then
            (key, pairs @ [(right, value)]) :: rest
          else
            (key, pairs) ::
              add_group ((left, right, value), rest)

    fun curry_fun source_domain left_ty right_ty source_range candidate =
      let
        fun triples pairs = map (fn (point, value) =>
          let val (left, right) =
            split_point source_domain left_ty right_ty point
          in (left, right, value) end) pairs
        fun grouped pairs = List.foldl add_group [] (triples pairs)
        fun ordinary marker pairs =
          let
            val groups = grouped pairs
            val inner_base = marker_with_type source_range marker
            fun inner entries = make_display_fun right_ty inner_base entries
            val outer_base = make_display_fun right_ty inner_base []
          in
            make_display_fun left_ty outer_base
              (map (fn (left, entries) => (left, inner entries)) groups)
          end
        fun set_value entries = make_literal_set right_ty
          (map #1 entries)
      in
        case Lib.total dest_display_fun candidate of
            SOME (marker, pairs) => ordinary marker pairs
          | NONE =>
              (case dest_literal_set candidate of
                   SOME elements =>
                     if MFH.is_boolean_type source_range then
                       let
                         val groups = grouped
                           (map (fn element =>
                             (element, boolSyntax.T)) elements)
                         val outer_base = make_literal_set right_ty []
                       in
                         make_display_fun left_ty outer_base
                           (map (fn (left, entries) =>
                             (left, set_value entries)) groups)
                       end
                     else
                       raise err "format_fun" "set with non-boolean range"
                 | NONE => marker_with_type
                     (Type.-->(left_ty, Type.-->(right_ty, source_range)))
                     candidate)
      end

    fun uncurry_fun target_domain target_range candidate =
      case Lib.total dest_display_fun candidate of
          NONE => marker_with_type
            (Type.-->(target_domain, target_range)) candidate
        | SOME (outer_marker, outer_pairs) =>
          let
            fun expand (left, inner) =
              let
                val (inner_pairs, was_set) =
                  case Lib.total dest_display_fun inner of
                      SOME (_, pairs) => (pairs, false)
                    | NONE =>
                        (case dest_literal_set inner of
                             SOME elements =>
                               (map (fn element =>
                                  (element, boolSyntax.T)) elements, true)
                           | NONE => ([], false))
              in
                (map (fn (right, value) =>
                   (reshape_pair target_domain
                      (pairSyntax.mk_prod
                        (Term.type_of left, Term.type_of right))
                      (pairSyntax.mk_pair (left, right)), value)) inner_pairs,
                 was_set)
              end
            val expanded = map expand outer_pairs
            val pairs = List.concat (map #1 expanded)
            val empty_set_default =
              case dest_literal_set outer_marker of
                  SOME [] => true
                | _ => false
            val all_sets = MFH.is_boolean_type target_range andalso
              empty_set_default andalso List.all #2 expanded
          in
            if all_sets then
              make_literal_set target_domain
                (map #1 (List.filter
                  (fn (_, value) => Term.aconv value boolSyntax.T) pairs))
            else
              make_display_fun target_domain
                (deepest_marker target_range outer_marker) pairs
          end

    fun do_arrow target_domain target_range source_domain source_range
          candidate =
      case Lib.total dest_display_fun candidate of
          NONE => marker_with_type (Type.-->(target_domain, target_range))
            candidate
        | SOME (marker, pairs) =>
            make_display_fun target_domain
              (do_term target_range source_range marker)
              (map (fn (point, value) =>
                (do_term target_domain source_domain point,
                 do_term target_range source_range value)) pairs)

    and do_fun target_domain target_range source_domain source_range
          candidate =
      case factor_out_types target_domain source_domain of
          ((_, NONE), (_, NONE)) =>
            do_arrow target_domain target_range source_domain source_range
              candidate
        | ((_, NONE), (source_left, SOME source_right)) =>
            do_arrow target_domain target_range source_left
              (Type.-->(source_right, source_range))
              (curry_fun source_domain source_left source_right source_range
                 candidate)
        | ((target_left, SOME target_right), (_, NONE)) =>
            uncurry_fun target_domain target_range
              (do_arrow target_left
                 (Type.-->(target_right, target_range))
                 source_domain source_range candidate)
        | _ => raise err "format_fun" "incompatible function grouping"

    and do_term target source candidate =
      if Util.same_type target source then candidate
      else if MFH.is_fun_type target andalso MFH.is_fun_type source then
        let
          val (target_domain, target_range) = Type.dom_rng target
          val (source_domain, source_range) = Type.dom_rng source
        in
          do_fun target_domain target_range source_domain source_range
            candidate
        end
      else if MFH.is_pair_type target andalso MFH.is_pair_type source then
        if pairSyntax.is_pair candidate then
          let
            val source_tys = pair_leaves source
            val target_tys = pair_leaves target
            val source_terms = flatten_pair_term source candidate
            val _ = if length source_tys = length target_tys then ()
              else raise err "format_fun" "tuple arities differ"
            val converted = ListPair.map
              (fn (target_ty, (source_ty, source_term)) =>
                do_term target_ty source_ty source_term)
              (target_tys, ListPair.zip (source_tys, source_terms))
            val (result, rest) = build_pair_term target converted
          in
            if null rest then result
            else raise err "format_fun" "unused converted tuple leaves"
          end
        else
          marker_with_type target candidate
      else
        marker_with_type target candidate
  in
    do_term target_ty (Term.type_of term) term
  end

fun lhs_for_constant special_funs name ty =
  user_friendly_const special_funs name ty

fun assignment_operator name =
  if MFN.is_ubfp_name name then "≤"
  else if MFN.is_lbfp_name name then "≥"
  else "="

fun eval_index name = MFN.eval_index name

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
            val (left, right) = boolSyntax.dest_eq body
          in
            if Term.aconv left variable then
              unfold_outer_the_binders
                (Term.beta_conv
                   (Term.mk_comb (Term.mk_abs (variable, right), term)))
            else term
          end handle HOL_ERR _ => term
        else term
    | NONE => term

fun has_codatatype_subtype co_types ty =
  List.exists (Util.same_type ty) co_types orelse
  (not (Type.is_vartype ty) andalso
   List.exists (has_codatatype_subtype co_types)
     (#Args (Type.dest_thy_type ty)))

fun bisimilar_values _ 0 _ = true
  | bisimilar_values co_types max_depth (left, right) =
      let
        val ty = Term.type_of left
      in
        if not (Util.same_type ty (Term.type_of right)) then false
        else if has_codatatype_subtype co_types ty then
          let
            val (left_head, left_args) =
              HolKernel.strip_comb (unfold_outer_the_binders left)
            val (right_head, right_args) =
              HolKernel.strip_comb (unfold_outer_the_binders right)
            val next_depth = max_depth -
              (if List.exists (Util.same_type ty) co_types then 1 else 0)
          in
            Term.aconv left_head right_head andalso
            ListPair.allEq
              (bisimilar_values co_types next_depth)
              (left_args, right_args)
          end
        else
          Term.aconv left right
      end

fun reconstruct_with formatting
      {scope, atoms, special_funs, real_frees, eval_terms,
       free_names, sel_names, nonsel_names, rel_table, bounds} =
  let
    (* One immutable callback snapshot governs the entire displayed model.
       Raw terms below never consult it and remain suitable for
       certification. *)
    val postprocessors = snapshot_term_postprocessors ()
    val context =
      {scope = scope, atoms = atoms, sel_names = sel_names,
       rel_table = rel_table, bounds = bounds,
       atom_avoids = List.concat
         (map Term.free_vars_lr (real_frees @ eval_terms)),
       pool = new_atom_pool ()}

    fun decode name =
      case MFNT.rep_of name of
          MFR.Any => MFN.unknown_marker
            (MFH.uniterize_unarize_unbox_etc_type (MFNT.type_of name))
        | representation => reconstruct_term context
            (not (MFNT.is_fully_representable_set name))
            (MFNT.type_of name) representation
            (tuples_for_name context name)

    fun formatted_value key value =
      case formatting of
          NONE => value
        | SOME (format_context, formats) =>
            format_fun (format_term_type format_context formats key) value

    fun binding term =
      let val name = free_name_for_term free_names term
          val value = decode name
      in ((term, value), (term, formatted_value term value)) end

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
              val leading = List.take (variables, prefix)
              val tuple = List.take (List.drop (variables, prefix), count)
              val trailing = List.drop (variables, prefix + count)
              val body = Term.list_mk_comb
                (value, leading @ [pairSyntax.list_mk_pair tuple] @ trailing)
            in
              MFH.eta_contract (Term.list_mk_abs (variables, body))
            end

    fun classify (name, ((evals, skolems, consts),
                         (display_evals, display_skolems,
                          display_consts))) =
      let
        val nickname = MFNT.nickname_of name
        val raw_value = decode name
        val lhs = lhs_for_constant special_funs nickname
          (MFNT.type_of name)
        val ordinary_value = curry_uncurried_value nickname
          (Term.type_of lhs) raw_value
        val display_value =
          case formatting of
              NONE => ordinary_value
            | SOME (format_context, formats) => format_fun
                (format_term_type_for_name format_context formats special_funs
                  nickname lhs) raw_value
      in
        if MFNT.is_skolem_name name then
          ((evals, (MFN.original_name nickname, ordinary_value) :: skolems,
            consts),
           (display_evals,
            (MFN.original_name nickname, display_value) :: display_skolems,
            display_consts))
        else
          case eval_index nickname of
              SOME index =>
                if index < length eval_terms then
                  let val eval_term = List.nth (eval_terms, index)
                  in
                    (((eval_term, ordinary_value) :: evals,
                      skolems, consts),
                     ((eval_term, formatted_value eval_term ordinary_value) ::
                        display_evals,
                      display_skolems, display_consts))
                  end
                else
                  ((evals, skolems, consts),
                   (display_evals, display_skolems, display_consts))
            | NONE =>
                ((evals, skolems,
                  (lhs, assignment_operator nickname, ordinary_value) ::
                    consts),
                 (display_evals, display_skolems,
                  (lhs, assignment_operator nickname, display_value) ::
                    display_consts))
      end

    fun is_bisim_support name =
      let val nickname = MFNT.nickname_of name
      in
        nickname = "refute$bisim" orelse
        nickname = "refute$bisim_iterator_max"
      end

    val displayed_names = List.filter (not o is_bisim_support) nonsel_names
    val ((evals, skolems, consts),
         (display_evals, display_skolems, display_consts)) =
      List.foldl classify (([], [], []), ([], [], [])) displayed_names

    fun values_for_type (spec : MFS.data_type_spec) =
      let
        val ty = #typ spec
        val card = #card spec
        val offset = MFS.offset_of_type (#ofs scope) ty
        val values = List.tabulate (card, fn index =>
          reconstruct_term context false ty (MFR.Atom (card, offset))
            [[offset + index]])
        val complete = Util.fun_from_pair (#complete spec) false
      in
        (ty, values, complete)
      end

    val deep_types = List.filter #deep (#data_types scope)
    fun has_type ty = List.exists (fn (spec : MFS.data_type_spec) =>
      Util.same_type (#typ spec) ty) deep_types
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
    val (bindings, display_bindings) = ListPair.unzip (map binding real_frees)
    fun result bindings evals skolems consts types =
      {bindings = bindings, evals = rev evals, skolems = rev skolems,
       consts = rev consts, types = types, codatatypes_ok = codatatypes_ok}
    fun process_pair (key, value) =
      (key, postprocess_term postprocessors value)
    fun process_skolem (name, value) =
      (name, postprocess_term postprocessors value)
    fun process_const (left, operator, value) =
      (left, operator, postprocess_term postprocessors value)
    fun process_type (ty, values, complete) =
      (ty, map (postprocess_term postprocessors) values, complete)
    fun displayed_result () = result
      (map process_pair display_bindings)
      (map process_pair display_evals)
      (map process_skolem display_skolems)
      (map process_const display_consts)
      (map process_type types)
  in
    {raw = result bindings evals skolems consts types,
     displayed =
       (case formatting of
            NONE => result display_bindings display_evals display_skolems
              display_consts types
          | SOME _ => displayed_result ()),
     postprocessors = postprocessors}
  end

fun reconstruct arguments = #raw (reconstruct_with NONE arguments)

fun reconstruct_both
      {context, formats, scope, atoms, special_funs, real_frees, eval_terms,
       free_names, sel_names, nonsel_names, rel_table, bounds} =
  reconstruct_with (SOME (context, formats))
    {scope = scope, atoms = atoms, special_funs = special_funs,
     real_frees = real_frees, eval_terms = eval_terms,
     free_names = free_names, sel_names = sel_names,
     nonsel_names = nonsel_names, rel_table = rel_table, bounds = bounds}

fun reconstruct_formatted arguments = #displayed (reconstruct_both arguments)

fun model_report ({skolems, consts, types, ...} : reconstruction) =
  {skolems = skolems, consts = consts, types = types}

fun display_counterexample postprocessors
      (reconstructed : reconstruction)
      (cex : Refute_Core.counterexample) : Refute_Core.counterexample =
  let
    fun displayed_value entries (key, value) =
      case List.find (fn (candidate, _) => Term.aconv candidate key)
             entries of
          SOME (_, displayed) =>
            if is_unknown displayed then
              (key, displayed)
            else if Util.same_type
              (Term.type_of value) (Term.type_of displayed) then
              (key, postprocess_term postprocessors value)
            else
              (key, postprocess_term postprocessors
                (Option.getOpt
                  (Lib.total (format_fun (Term.type_of displayed)) value,
                   displayed)))
        | NONE => (key, postprocess_term postprocessors value)
  in
    {backend = #backend cex, substrate = #substrate cex,
     certainty = #certainty cex,
     bindings = map (displayed_value (#bindings reconstructed))
       (#bindings cex),
     evals = map (displayed_value (#evals reconstructed)) (#evals cex),
     cert = #cert cex, scope = #scope cex,
     model = SOME (model_report reconstructed), stats = #stats cex}
  end

fun replace_irrelevant term =
  if combinSyntax.is_K_1 term then
    let
      val body = combinSyntax.dest_K_1 term
      val (domain_ty, _) = Type.dom_rng (Term.type_of term)
    in
      if MFN.is_irrelevant_marker body then
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
fun certification_copy scope types original eval_terms bindings =
  let
    val tyvars = Lib.U (map Term.type_vars_in_term
      (original :: eval_terms @
       List.concat (map (fn (left, right) => [left, right]) bindings)))
    fun scope_card ty =
      case scope of
          SOME assignments =>
            Option.map #2 (List.find (fn (other, _) => Util.same_type ty other)
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
              fun atom_substitutions (tyvar, card) =
                case List.find (fn (other, _, _) =>
                    Util.same_type tyvar other) types of
                    SOME (_, atoms, _) =>
                      if length atoms = card then
                        SOME (ListPair.mapEq (fn (atom, index) =>
                          (atom, rf_constructor card index))
                          (atoms, Portable.upto 1 card))
                      else NONE
                  | NONE => NONE
              fun collect_atoms [] = SOME []
                | collect_atoms (row :: rest) =
                    (case (atom_substitutions row, collect_atoms rest) of
                         (SOME atoms, SOME others) => SOME (atoms @ others)
                       | _ => NONE)
            in
              case collect_atoms rows of
                  NONE => NONE
                | SOME atom_images =>
                    let
                      (* Do not form atom-substitution keys after [theta]:
                         distinct type variables of equal cardinality then
                         share an rf type and can have identically named
                         atoms.  Temporary source-typed variables preserve
                         their identities through instantiation. *)
                      val avoids = List.concat
                        (map Term.all_vars
                          (original :: eval_terms @
                           List.concat (map (fn (left, right) =>
                             [left, right]) bindings))) @
                        map #1 atom_images
                      fun fresh_atoms [] _ _ source target =
                            (rev source, rev target)
                        | fresh_atoms ((atom, image) :: rest) serial avoids
                            source target =
                            let val temporary = Term.variant avoids
                              (Term.mk_var
                                (MFN.reserved_prefix ^ "cert_atom" ^
                                 Int.toString serial, Term.type_of atom))
                            in
                              fresh_atoms rest (serial + 1)
                                (temporary :: avoids)
                                ({redex = atom, residue = temporary} :: source)
                                ({redex = Term.inst theta temporary,
                                  residue = image} :: target)
                            end
                      val (source_atoms, target_atoms) =
                        fresh_atoms atom_images 0 avoids [] []
                      fun copy_value value = Term.subst target_atoms
                        (Term.inst theta
                          (Term.subst source_atoms (replace_irrelevant value)))
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

fun fallback_certainty sound genuine reasons =
  if sound andalso genuine then Refute_Core.Genuine
  else if sound then Refute_Core.QuasiGenuine reasons
  else Refute_Core.Potential reasons

fun certify {executable, original, eval_terms,
             reconstruction = reconstructed, cex, sound,
             genuine_means_genuine = genuine, reasons} =
  let
    val {bindings, evals, types, codatatypes_ok, ...} = reconstructed
    val genuine = genuine andalso codatatypes_ok
    val model = SOME (model_report reconstructed)
    val base = replace_cex cex (fallback_certainty sound genuine reasons)
      bindings evals NONE model
  in
    case if executable andalso codatatypes_ok then
           certification_copy (#scope cex) types original eval_terms
             bindings
         else NONE of
        NONE => Keep base
      | SOME {original = cert_original, eval_terms = cert_evals,
              env, polymorphic} =>
          (case Refute_Cert.certify
              {original = cert_original, evals = cert_evals, env = env,
               cex = base} of
               Refute_Cert.Certified certified =>
                 (* A genuine result may display only values established by
                    the kernel certificate.  Decoded solver values are
                    useful reconstruction data, but are not certificates. *)
                 Keep (replace_cex certified Refute_Core.Genuine bindings
                   (#evals certified) (#cert certified) NONE)
             | Refute_Cert.Potential potential =>
                 Keep (replace_cex potential (#certainty potential) bindings
                   evals NONE model)
             | Refute_Cert.Discarded =>
                 (* Kernel evaluation has established that this assignment
                    does not falsify the goal; it cannot be a counterexample
                    at any certainty level. *)
                 (if sound then
                    Refute_Core.Private.say 1
                      "Refute warning: certification refuted the model\n"
                  else ();
                  Drop))
  end

end
