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

  type replay_hint =
    {value : term,
     provenance : Refute_Cert_Model.provenance option}

  datatype replay_hole_display =
      DisplayUnknown
    | DisplayIrrelevant
    | DisplayUnrepresented
    | DisplayFunctionFallback

  datatype replay_hole_origin =
      AnyRepresentation
    | OptionalAbsent
    | IncompleteFunctionFallback
    | UnknownFunctionPoint
    | PartialSetMembership
    | UnrepresentedSetElement
    | FunctionDefault

  type replay_hole =
    {id : int,
     variable : term,
     display : replay_hole_display,
     origin : replay_hole_origin}

  type replay_sidecar = {holes : replay_hole list}

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
  val postprocess_term : term_postprocessor_snapshot -> term -> term
  (* [Refute_Gen] has no dependency on this structure, so a generator
     family's canonical display snapshot is threaded in as a callback
     instead of registered directly; see [Refute.sml], which depends on
     both and installs [Refute_Gen.snapshot_family_canonicals] here, on the
     same precedent as [Refute_Core.register_backend] and
     [register_mono_instance_transform]. *)
  val register_family_canonical_lookup :
    (unit -> hol_type -> term_postprocessor option) -> unit
  val register_frac_type_rat : unit -> unit
  (* Installed by default (see Refute.sml).  Idempotent, like
     [register_frac_type_rat]. *)
  val register_frac_type_real : unit -> unit
  (* Installed by default (see Refute.sml).  Idempotent, like
     [register_frac_type_rat]; unlike the frac registrations there is
     only one fmap display, valid at every [:'a |-> 'b] instance. *)
  val register_fmap_display : unit -> unit
  (* Installed by default (see Refute.sml).  Idempotent, like
     [register_fmap_display]; valid at every function type. *)
  val register_function_display : unit -> unit

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
     certification : reconstruction,
     displayed : reconstruction,
     replay_hints : replay_hint list,
     replay_sidecar : replay_sidecar,
     postprocessors : term_postprocessor_snapshot}

  val model_report : reconstruction -> Refute_Core.model_report
  val display_counterexample :
    term_postprocessor_snapshot -> reconstruction ->
    Refute_Core.counterexample -> Refute_Core.counterexample
  val assignment_operator : string -> string
  val certification_env_with_holes :
    replay_sidecar -> (term * term) list -> (term * term) list option
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
     certification : reconstruction,
     replay_sidecar : replay_sidecar,
     replay_hints : replay_hint list,
     cex : Refute_Core.counterexample,
     sound : bool,
     genuine_means_genuine : bool,
     reasons : string list,
     deadline : Time.time option} -> verdict
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
type term = Term.term
type hol_type = Type.hol_type
type rep = MFR.rep
type nut = MFNT.nut
type scope = MFS.scope
type raw_bound = Refute_Forl.raw_bound

structure Util = Refute_ModelFinder_Util

type replay_hint =
  {value : term,
   provenance : Refute_Cert_Model.provenance option}

datatype replay_hole_display =
    DisplayUnknown
  | DisplayIrrelevant
  | DisplayUnrepresented
  | DisplayFunctionFallback

datatype replay_hole_origin =
    AnyRepresentation
  | OptionalAbsent
  | IncompleteFunctionFallback
  | UnknownFunctionPoint
  | PartialSetMembership
  | UnrepresentedSetElement
  | FunctionDefault

type replay_hole =
  {id : int,
   variable : term,
   display : replay_hole_display,
   origin : replay_hole_origin}

type replay_sidecar = {holes : replay_hole list}

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
type term_postprocessor_registry =
  {entries : term_postprocessor_entry list, next_serial : int}

(* A snapshot pairs the pattern registry with an immutable family lookup,
   so one model display sees one coherent view of both sources instead of a
   stable registry mixed with a family lookup that can move mid-walk. *)
type term_postprocessor_snapshot =
  {registry : term_postprocessor_registry,
   family : hol_type -> term_postprocessor option}

(* Model display extensions are process-local ML data.  The registry uses
   type patterns: every pattern that matches an actual type participates.
   Composition is deterministic: general patterns run before strictly more
   specific patterns, and otherwise older registrations run before newer
   ones.  Re-registering an alpha-equivalent pattern replaces its callback
   without adding a duplicate or changing its established position. *)
val term_postprocessors = ref
  ({entries = [], next_serial = 0} : term_postprocessor_registry)

fun with_term_postprocessor_lock body = MFH.with_registration_lock body

(* Settable snapshot hook for generator-family canonical display forms
   (Refute_Gen.sml).  Defaults to "no family registered anything";
   [Refute.sml] installs the real snapshot provider at load time (see the
   signature comment on
   [register_family_canonical_lookup]). *)
val family_canonical_lookup :
    (unit -> hol_type -> term_postprocessor option) ref =
  ref (fn () => fn (_ : hol_type) => NONE)

fun register_family_canonical_lookup f =
  with_term_postprocessor_lock (fn () => family_canonical_lookup := f)

fun snapshot_term_postprocessors () =
  with_term_postprocessor_lock (fn () =>
    {registry = !term_postprocessors,
     family = (!family_canonical_lookup) ()})

fun pattern_matches pattern actual =
  Lib.can (Type.match_type pattern) actual

fun same_pattern left right =
  pattern_matches left right andalso pattern_matches right left

fun strictly_more_general left right =
  pattern_matches left right andalso not (pattern_matches right left)

fun matching_postprocessors
      ({entries, ...} : term_postprocessor_registry) actual =
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

(* One walk, two registration sources: the pattern registry above (user
   patterns and the model finder's own built-ins, e.g. fmap rep unwrapping)
   runs first, then the family hook's canonical form (e.g. fmap's own
   FUPDATE-chain dedup) -- so a fmap rep atom is unwrapped into a chain by
   the former before the latter dedups it.  Both go through the identical
   [safe_postprocess] contract: this is the single copy of it.  Both
   sources are read from [snapshot], never from a live global: that is
   what makes one registry snapshot mean one coherent view of the whole
   model, and it avoids taking [Refute_Gen]'s registration mutex (behind
   [family]) at every term node of every model. *)
fun composed_postprocessor
      (snapshot : term_postprocessor_snapshot) ty =
  let
    val pattern_postprocessors =
      matching_postprocessors (#registry snapshot) ty
    val family_postprocessor =
      case (#family snapshot) ty of
          SOME postprocessor => [postprocessor]
        | NONE => []
    val postprocessors = pattern_postprocessors @ family_postprocessor
  in
    case postprocessors of
        [] => NONE
      | _ => SOME (fn term =>
          List.foldl (fn (postprocessor, candidate) =>
            safe_postprocess postprocessor candidate) term postprocessors)
  end

fun lookup_term_postprocessor ty =
  composed_postprocessor (snapshot_term_postprocessors ()) ty

fun insert_postprocessor pattern postprocessor
      ({entries, next_serial} : term_postprocessor_registry) =
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

fun postprocess_term (snapshot : term_postprocessor_snapshot) term =
  let
    (* One entry per distinct type: [composed_postprocessor] runs a
       [Type.match_type] per registry entry and a sort on the matches, while
       a model term has orders of magnitude more nodes than distinct types.
       [snapshot] is fixed here, so the answer depends only on the type. *)
    val composed = ref (Redblackmap.mkDict Type.compare)
    fun postprocessor_for ty =
      case Redblackmap.peek (!composed, ty) of
          SOME entry => entry
        | NONE =>
            let val entry = composed_postprocessor snapshot ty in
              composed := Redblackmap.insert (!composed, ty, entry);
              entry
            end
    fun apply candidate =
      case postprocessor_for (Term.type_of candidate) of
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
    (* The family half of [snapshot] is never checked here: [Refute.sml]
       installs both it and the four built-in pattern entries together,
       unconditionally, at load, and the public surface exposes no way to
       remove a pattern entry, so [#entries] is never empty in a real
       session -- this is purely a fast path for that case, not a
       correctness gate. *)
    val nothing_registered = null (#entries (#registry snapshot))
  in
    if nothing_registered then term else descend term
  end

(* The recognition contract shared by both frac renderers below: a
   reconstructed [abs_frac] atom over a pair of integer literals.
   [raw_constructor_name] deliberately covers reconstructed variables as well
   as constants: the atom reaching this postprocessor is usually a variable
   whose stripped name is the mangled constant, so a [dest_thy_const] test
   here would silently stop matching. *)
fun dest_frac_atom term =
  case HolKernel.strip_comb term of
      (constructor, [pair]) =>
        if MFH.raw_constructor_name constructor = "frac$abs_frac" then
          let
            val (numerator, denominator) = pairSyntax.dest_pair pair
          in
            if Util.same_type (Term.type_of numerator) MFH.int_type andalso
               Util.same_type (Term.type_of denominator) MFH.int_type
            then SOME (numerator, denominator)
            else NONE
          end handle HOL_ERR _ => NONE
        else
          NONE
    | _ => NONE

fun frac_atom_to_rat term =
  case dest_frac_atom term of
      NONE => term
    | SOME (numerator, denominator) =>
        (let
           val rat_cons = Term.prim_mk_const {Thy = "rat", Name = "rat_cons"}
           val denominator =
             if Arbint.compare
                  (intSyntax.int_of_term numerator, Arbint.zero) = EQUAL
             then intSyntax.term_of_int Arbint.one
             else denominator
         in
           Term.list_mk_comb (rat_cons, [numerator, denominator])
         end handle HOL_ERR _ => term)

(* [realax$real] has no literal constructor the way [rat$rat_cons] does, so
   a reconstructed [abs_frac] value is rendered through division instead: a
   zero numerator or a denominator of [1] prints as the bare numerator
   (a real model value must print as [3], never [3 / 1]), any other
   denominator prints as [realSyntax.mk_div] of the two rendered integers.
   That is a deliberate divergence from [frac_atom_to_rat], which always
   prints [n // d]; it is not an oversight to "fix" back into symmetry. *)
fun frac_atom_to_real term =
  case dest_frac_atom term of
      NONE => term
    | SOME (numerator, denominator) =>
        (let
           val numerator_int = intSyntax.int_of_term numerator
           val denominator_int = intSyntax.int_of_term denominator
           val numerator_term = realSyntax.term_of_int numerator_int
         in
           if Arbint.compare (numerator_int, Arbint.zero) = EQUAL orelse
              Arbint.compare (denominator_int, Arbint.one) = EQUAL
           then numerator_term
           else
             realSyntax.mk_div
               (numerator_term, realSyntax.term_of_int denominator_int)
         end handle HOL_ERR _ => term)

(* Narrowed to [:real] by type, not by the reserved name alone: [abs_frac]
   is [int # int -> frac] (retypes to neither [real] nor [rat]), so [rat]
   hits the identical opaque-reserved-variable fallback and a bare name
   match would also authorize it.  [MFN.original_name] alone is not
   enough either: it strips every generated-name layer, so a selector or
   discriminator wrapping the same tail ([refute$sel0$frac$abs_frac])
   would match too, hence the explicit [not (MFN.is_sel name)].  This
   predicate need not discriminate precisely for soundness - see
   [certification_env_with_holes] below: a qualifying binding is dropped,
   not trusted. *)
fun qualifying_frac_head head =
  case Lib.total Term.dest_var head of
      SOME (name, _) =>
        MFN.is_reserved_name name andalso not (MFN.is_sel name) andalso
        MFN.original_name name = "frac$abs_frac"
    | NONE => false

fun qualifying_frac_binding (variable, value) =
  Util.same_type (Term.type_of variable) realSyntax.real_ty andalso
  Util.same_type (Term.type_of value) realSyntax.real_ty andalso
  (case HolKernel.strip_comb value of
       (head, [pair]) =>
         qualifying_frac_head head andalso
         (case Lib.total pairSyntax.dest_pair pair of
              SOME (n, d) =>
                intSyntax.is_int_literal n andalso
                intSyntax.is_int_literal d andalso
                let val converted = frac_atom_to_real value in
                  not (Term.aconv converted value) andalso
                  null (Term.free_vars converted)
                end
            | NONE => false)
     | _ => false)

fun prepare_frac_term_postprocessor pattern postprocessor =
  let
    val updated = insert_postprocessor pattern postprocessor
      (!term_postprocessors)
  in
    fn () => term_postprocessors := updated
  end

(* Shared two-phase commit for every Frac-carrier registration: the Frac
   classification and its display postprocessor are prepared (validated,
   with every replacement precomputed) before either registry is touched,
   then committed together under one uninterruptible section so an
   interrupt cannot leave the encoding registered without its display
   transform, or vice versa.  [MFH.prepare_frac_type_unlocked], not a
   locking variant, is correct here because [with_term_postprocessor_lock]
   *is* [MFH.with_registration_lock] (see above): both prepare steps are
   callback-free and already run under that one shared mutex, so a locking
   variant would deadlock. *)
fun register_frac_type_with_display (frac_info, pattern, postprocessor) =
  with_term_postprocessor_lock (fn () =>
    let
      val commit_frac = MFH.prepare_frac_type_unlocked frac_info
      val commit_postprocessor =
        prepare_frac_term_postprocessor pattern postprocessor
    in
      Thread_Attributes.uninterruptible (fn _ => fn () =>
        (commit_frac ();
         commit_postprocessor ())) ()
    end)

fun register_frac_type_rat () =
  register_frac_type_with_display
    (MFH.rat_frac_registration,
     Type.mk_thy_type {Thy = "rat", Tyop = "rat", Args = []},
     frac_atom_to_rat)

fun register_frac_type_real () =
  register_frac_type_with_display
    (MFH.real_frac_registration,
     Type.mk_thy_type {Thy = "realax", Tyop = "real", Args = []},
     frac_atom_to_real)

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

type replay_hole_pool =
  {next : int,
   holes : replay_hole list} ref

fun new_replay_hole_pool () : replay_hole_pool =
  ref {next = 0, holes = []}

type context =
  {scope : scope,
   atoms : (hol_type option * string list) list,
   sel_names : nut list,
   rel_table : nut MFNT.NameTable.table,
   bounds : raw_bound list,
   atom_avoids : term list,
   pool : atom_pool,
   replay_holes : replay_hole_pool}

fun err function message =
  Feedback.mk_HOL_ERR "Refute_ModelFinder_Model" function message

fun fresh_replay_hole ({replay_holes, ...} : context) display origin ty =
  let
    val {next, holes} = !replay_holes
    val variable = MFN.mk_replay_hole next ty
    val hole =
      {id = next, variable = variable, display = display, origin = origin}
  in
    replay_holes := {next = next + 1, holes = hole :: holes};
    variable
  end

fun set_replay_hole_origin ({replay_holes, ...} : context) variable origin =
  let
    val {next, holes} = !replay_holes
    fun update (hole as
          {id, variable = candidate, display, origin = old} : replay_hole) =
      if Term.aconv candidate variable then
        {id = id, variable = candidate, display = display, origin = origin}
      else
        hole
  in
    replay_holes := {next = next, holes = map update holes}
  end

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

fun tuples_for_name ({rel_table, bounds, ...} : context) name =
  let val relation = MFNT.the_rel rel_table name
  in Option.getOpt (AList.lookup (op =) bounds relation, []) end
  handle MFNT.NUT _ => [[]]

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
    val requested =
      if MFN.is_replay_hole_name (#1 (Term.dest_var requested)) then
        Term.mk_var ("user$" ^ #1 (Term.dest_var requested), ty)
      else
        requested
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

fun make_update (point, value) base =
  Term.mk_comb (combinSyntax.mk_update (point, value), base)

fun make_fun (context as {scope, ...} : context) actual_domain_ty
      display_domain_ty display_range_ty pairs =
  let
    val complete = MFS.is_complete_type (#data_types scope) false
      actual_domain_ty
    val origin =
      if complete then FunctionDefault else IncompleteFunctionFallback
    (* A function-valued hole leaves different unspecified points
       independent.  The public renderer spells such a hole [K ?]/[K _]
       and hides direct unknown-valued rows. *)
    val base = fresh_replay_hole context DisplayFunctionFallback origin
      (Type.-->(display_domain_ty, display_range_ty))
    val _ = List.app (fn (_, value) =>
      if MFN.is_replay_hole value then
        set_replay_hole_origin context value UnknownFunctionPoint
      else ()) pairs
  in
    List.foldl (fn (pair, result) => make_update pair result)
      base (sort_terms pairs)
  end

fun make_set (context as {scope, ...} : context) maybe_opt actual_element_ty
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
        present @ [fresh_replay_hole context DisplayUnrepresented
          UnrepresentedSetElement display_element_ty]
      else
        present
    fun insert (element, set) = pred_setSyntax.mk_insert (element, set)
  in
    (* An exact set asserts every omitted member is absent.  Retaining the
       true tuples while discarding unknown memberships would therefore make
       a solver partiality look like a negative fact. *)
    if has_unknown then
      fresh_replay_hole context DisplayUnknown PartialSetMembership
        (pred_setSyntax.mk_set_type display_element_ty)
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
          (MFR.Any, _) => fresh_replay_hole context DisplayUnknown
            AnyRepresentation (MFH.uniterize_unarize_unbox_etc_type ty)
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
              fun range chunk =
                let
                  val value = MFH.unarize_unbox_etc_term
                    (term_for_rep true seen range_ty range_rep [chunk])
                  val _ = case range_rep of
                      MFR.Any => set_replay_hole_origin context value
                        UnknownFunctionPoint
                    | _ => ()
                in value end
              val ranges = map range chunks
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
                if Lib.mem tuple tuples then boolSyntax.T
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
              fun range tuple =
                let
                  val value = MFH.unarize_unbox_etc_term
                    (term_for_rep false seen range_ty range_rep
                      (tails tuple))
                  val _ = case range_rep of
                      MFR.Any => set_replay_hole_origin context value
                        UnknownFunctionPoint
                    | _ => ()
                in value end
              val ranges = map range combinations
            in
              make_fun_or_set context maybe_opt ty
                (ListPair.zip (domains, ranges))
            end
        | (MFR.Opt inner, []) => fresh_replay_hole context DisplayUnknown
            OptionalAbsent (MFH.uniterize_unarize_unbox_etc_type ty)
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
            else if MFH.is_word_type ty then
              (* Atom [j] of a word carrier denotes [n2w j], which prints in
                 the surface literal form. *)
              wordsSyntax.mk_n2w
                (numSyntax.term_of_int atom, wordsSyntax.dest_word_type ty)
            else if MFH.is_char_type ty then
              (* Atom [j] denotes [CHR j], which the printer renders as the
                 character literal. *)
              stringSyntax.mk_chr (numSyntax.term_of_int atom)
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
        val display_ty = MFH.unarize_unbox_etc_type ty
        val cycle = Term.mk_var
          (MFN.reserved_prefix ^ "cycle" ^ Int.toString atom, display_ty)
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
                Lib.mem [real_atom] (tuples_for_name context name)
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
            val omega = Term.mk_var (MFN.cyclic_co_val_name, display_ty)
            val unfolded = Term.subst [{redex = cycle, residue = omega}] body
            val predicate = Term.mk_abs
              (omega, boolSyntax.mk_eq (omega, unfolded))
            val choice = Term.mk_thy_const
              {Thy = "refute", Name = "safe_The",
               Ty = Type.-->(Type.-->(display_ty, Type.bool), display_ty)}
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
            (* Nested bitwords are already decoded to num or int.  Undoing
               that decoding on the constructor's own type is what lets a
               binarized Abs be a registered constant again. *)
            val value = Term.list_mk_comb
              (MFH.restore_retyped_constant
                 (MFH.unarize_unbox_etc_term constructor),
               map MFH.unarize_unbox_etc_term (rev arguments))
          in
            if co andalso Term.free_in cycle value then safe_the value
            else value
          end
      end
  in
    MFH.unarize_unbox_etc_term
      (term_for_rep maybe_opt [] ty representation tuples)
  end

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

(* fmap's synthetic rep is [key -> range option]
   (synthetic_fmap_typedef, Refute_ModelFinder_HOL.sml), so a
   reconstructed [abs_fmap' f] displays through [dest_display_fun]'s
   generic update-chain parser exactly like any other reconstructed
   function value.  The chain's base case must be safe to render as
   [NONE]: either it already is the literal [NONE], or it is
   [MFN.irrelevant_marker] -- a hole the reconstruction has already
   certified as fillable with *any* well-typed value without changing
   the verdict (Refute_ModelFinder_Names.sml), so [NONE] is one sound
   choice among the ones that hole permits.  [MFN.unknown_marker] gets
   no such license: unlike [DisplayIrrelevant], [DisplayUnknown] does
   not promise every filling is safe, so treating it as [NONE] could
   show a different map than the one certified -- decline instead.
   The same reasoning applies per explicit point: a value is rendered
   only when it is the literal [NONE] or [SOME v]; if any named point's
   value is itself an opaque marker, the whole rewrite is declined
   rather than guessing whether that point is present.  Kept points are
   rendered via [pairs] in the order [dest_display_fun] returns them,
   innermost first, so the outermost (highest-priority) update lands
   last and wins ties exactly as it does in the rep chain -- making the
   result denote the identical rep function, and hence (abs_fmap' being
   a bijection on such reps) the identical fmap atom.  That relies on
   each key occurring at most once: [binding] below drops a [NONE]
   point rather than emitting an [FUPDATE] for it, which is only sound
   when no later point re-adds that same key -- a duplicate key with a
   [NONE] point after a [SOME v] one would otherwise silently keep the
   stale [v] instead of the point that actually wins.  [pairs] is
   therefore checked for a duplicate key first, and the whole rewrite
   is declined (not guessed at) if one is found.  A key carrying a
   display marker is never counted as a duplicate of another, even an
   [aconv]-equal one: the same policy [dedup_update_chain] applies to
   the rep chain below this node, for the same reason (a marker stands
   for an unspecified value, so two occurrences are never known to
   collide).  Genuine (marker-free) duplicate keys are defensive only:
   [dedup_update_chain] already dedups the rep chain bottom-up before
   this node runs, so [dest_display_fun] cannot currently surface one. *)
fun has_duplicate_key pairs =
  let
    val seen = Util.aconv_member
  in
    #1 (List.foldl
      (fn ((key, _), (dup, prior)) =>
         if MFN.contains_display_marker key then (dup, prior)
         else (dup orelse seen key prior, key :: prior))
      (false, []) pairs)
  end

fun fmap_atom_to_chain term =
  (case HolKernel.strip_comb term of
      (constructor, [rep]) =>
        if MFH.raw_constructor_name constructor = "refute$abs_fmap'" then
          (case Lib.total dest_display_fun rep of
               SOME (marker, pairs) =>
                 (* Declining (not guessing) covers a base that is
                    [unknown_marker] rather than [NONE]/[irrelevant_marker];
                    [dest_display_fun] cannot currently produce that for a
                    fmap rep, so this branch is defensive only.  A genuine
                    duplicate key is likewise defensive only, per
                    [has_duplicate_key]'s comment above. *)
                 if Lib.can optionSyntax.dest_none marker orelse
                    MFN.is_irrelevant_marker marker
                 then
                   let
                     val (key_ty, option_ty) = Type.dom_rng (Term.type_of rep)
                     val range_ty = optionSyntax.dest_option option_ty
                     fun classify value =
                       if Lib.can optionSyntax.dest_none value then SOME NONE
                       else
                         Option.map SOME (Lib.total optionSyntax.dest_some
                           value)
                     val classified =
                       map (fn (key, value) => (key, classify value)) pairs
                   in
                     if has_duplicate_key pairs then term
                     else if List.all (isSome o #2) classified then
                       let
                         fun binding (key, SOME (SOME v)) =
                               SOME (pairSyntax.mk_pair (key, v))
                           | binding (_, _) = NONE
                         val bindings = List.mapPartial binding classified
                       in
                         finite_mapSyntax.list_mk_fupdate
                           (finite_mapSyntax.mk_fempty (key_ty, range_ty),
                            bindings)
                       end
                     else term
                   end
                 else term
             | NONE => term)
        else term
    | _ => term)
  handle HOL_ERR _ => term

(* fmap's typedef (synthetic_fmap_typedef, Refute_ModelFinder_HOL.sml)
   is itself unconditional, valid at every instance, so unlike the frac
   registrations there is no per-instance encoding to commit alongside
   the display: [register_term_postprocessor] alone suffices. *)
fun register_fmap_display () =
  register_term_postprocessor
    (finite_mapSyntax.mk_fmap_ty (Type.alpha, Type.beta))
    fmap_atom_to_chain

(* A raw function witness's update chain can carry a point shadowed by a
   later, higher-priority one: NativeSML's and Compute's own
   [exhaustive_function] (identical [layers] recursion in
   Refute_Extract.sml and Refute_EvalCompute.sml) and their random
   counterparts ([draw_points]) each pick a layer's/point's value
   independently, with no revisit guarantee.  Only
   [Refute_Gen.function_terms] -- reached solely when both the domain
   and range enumerate -- zips a domain enumeration and never repeats;
   that is a special case, not the general QC behaviour.  [strip_update]
   returns pairs outermost first, i.e. highest priority first, so keeping
   only the first occurrence of each [aconv] point and dropping the rest
   is exactly [canonical_fmap_chain]'s dedup (Refute.sml), generalized
   from fmap's [FUPDATE] to every function type; the base and every
   surviving point are left untouched, so no fresh binder or value is
   ever introduced.  A point carrying a display marker
   (MFN.contains_display_marker) is never deduped against another, even
   an [aconv]-equal one: a marker stands for an unspecified value, so
   two occurrences are never known to be the same point, and dropping
   either would silently lose a real row of the model.  Registered
   generically, this is the one seam both the model finder's own
   K_1-based reconstruction and a QC substrate's lambda-based witness go
   through alike. *)
fun dedup_update_chain term =
  let val (updates, base) = combinSyntax.strip_update term in
    if List.length updates < 2 then term
    else
      let
        fun keep ((point, value), (kept, seen)) =
          if MFN.contains_display_marker point then
            ((point, value) :: kept, seen)
          else if Util.aconv_member point seen then (kept, seen)
          else ((point, value) :: kept, point :: seen)
        val (kept_rev, _) = List.foldl keep ([], []) updates
        val kept = List.rev kept_rev
      in
        if List.length kept = List.length updates then term
        else
          List.foldr (fn ((point, value), result) =>
            Term.mk_comb (combinSyntax.mk_update (point, value), result))
            base kept
      end
  end

fun register_function_display () =
  register_term_postprocessor
    (Type.-->(Type.alpha, Type.beta)) dedup_update_chain

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

fun replay_hole_for holes term =
  if not (Term.is_var term) then NONE
  else
    let val name = #1 (Term.dest_var term)
    in
      List.find (fn ({variable, ...} : replay_hole) =>
        #1 (Term.dest_var variable) = name) holes
    end

fun render_replay_holes holes term =
  let
    fun marker DisplayUnknown ty = MFN.unknown_marker ty
      | marker DisplayIrrelevant ty = MFN.irrelevant_marker ty
      | marker DisplayUnrepresented ty =
          MFN.unrepresented_marker_ascii ty
      | marker DisplayFunctionFallback _ =
          raise err "render_replay_holes" "function hole used as scalar"

    fun project occurrence
          ({display = DisplayFunctionFallback, origin, ...} : replay_hole) =
          let
            val (domain_ty, range_ty) = Type.dom_rng (Term.type_of occurrence)
            val body =
              case origin of
                  FunctionDefault => MFN.irrelevant_marker range_ty
                | _ => MFN.unknown_marker range_ty
          in
            combinSyntax.mk_K_1 (body, domain_ty)
          end
      | project occurrence ({display, ...} : replay_hole) =
          marker display (Term.type_of occurrence)

    fun direct_unknown value =
      case replay_hole_for holes value of
          SOME ({display = DisplayUnknown, ...} : replay_hole) => true
        | _ => false

    fun render candidate =
      case replay_hole_for holes candidate of
          SOME hole => project candidate hole
        | NONE =>
            (case Lib.total combinSyntax.dest_update_comb candidate of
                 SOME ((point, value), base) =>
                   if direct_unknown value then render base
                   else make_update (render point, render value) (render base)
               | NONE =>
                   if Term.is_abs candidate then
                     let val (variable, body) = Term.dest_abs candidate
                     in Term.mk_abs (variable, render body) end
                   else
                     (case Lib.total Term.dest_comb candidate of
                          SOME (function, argument) =>
                            Term.mk_comb (render function, render argument)
                        | NONE => candidate))
  in
    render term
  end

fun reconstruction_terms
      ({bindings, evals, skolems, consts, types, ...} : reconstruction) =
  List.concat (map (fn (left, right) => [left, right]) bindings) @
  List.concat (map (fn (left, right) => [left, right]) evals) @
  map #2 skolems @
  List.concat (map (fn (left, _, right) => [left, right]) consts) @
  List.concat (map #2 types)

fun sidecar_for holes reconstruction : replay_sidecar =
  let
    val frees = Refute_Util.distinct_terms
      (List.concat (map Term.free_vars_lr
        (reconstruction_terms reconstruction)))
  in
    {holes = List.filter (fn ({variable, ...} : replay_hole) =>
       Util.aconv_member variable frees) holes}
  end

fun term_for_rep {scope, atoms, sel_names, rel_table, bounds, maybe_opt,
                  ty, representation, tuples} =
  let
    val replay_holes = new_replay_hole_pool ()
    val context =
      {scope = scope, atoms = atoms, sel_names = sel_names,
       rel_table = rel_table, bounds = bounds, atom_avoids = [],
       pool = new_atom_pool (), replay_holes = replay_holes}
    val private = reconstruct_term context maybe_opt ty representation tuples
  in
    render_replay_holes (rev (#holes (!replay_holes))) private
  end

fun reconstruct_with formatting
      {scope, atoms, special_funs, real_frees, eval_terms,
       free_names, sel_names, nonsel_names, rel_table, bounds} =
  let
    (* One immutable callback snapshot governs the displayed model.  The raw
       public view never consults callbacks; certification uses its separate
       private view containing sidecar-declared replay holes. *)
    val postprocessors = snapshot_term_postprocessors ()
    val skolem_infos =
      case formatting of
          SOME (format_context, _) => !(#skolems format_context)
        | NONE => []
    val context =
      {scope = scope, atoms = atoms, sel_names = sel_names,
       rel_table = rel_table, bounds = bounds,
       atom_avoids = List.concat
         (map Term.free_vars_lr (real_frees @ eval_terms)),
       pool = new_atom_pool (), replay_holes = new_replay_hole_pool ()}

    fun current_holes () = rev (#holes (!(#replay_holes context)))
    fun public_value value = render_replay_holes (current_holes ()) value

    fun decode name =
      case MFNT.rep_of name of
          MFR.Any => fresh_replay_hole context DisplayUnknown
            AnyRepresentation
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
          val private_value = decode name
          val raw_value = public_value private_value
      in
        ((term, private_value), (term, raw_value),
         (term, formatted_value term raw_value))
      end

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

    fun replay_provenance nickname =
      let
        val metadata_name = format_metadata_name nickname
        fun matches ({generated_name, ...} : MFH.skolem_info) =
          generated_name = metadata_name
      in
        List.find matches skolem_infos
      end

    fun classify (name,
          ((cert_evals, cert_skolems, cert_consts, replay_hints),
           (raw_evals, raw_skolems, raw_consts),
           (display_evals, display_skolems, display_consts))) =
      let
        val nickname = MFNT.nickname_of name
        val private_raw_value = decode name
        val raw_value = public_value private_raw_value
        val lhs = lhs_for_constant special_funs nickname
          (MFNT.type_of name)
        val private_value = curry_uncurried_value nickname
          (Term.type_of lhs) private_raw_value
        val raw_value = curry_uncurried_value nickname
          (Term.type_of lhs) raw_value
        val display_value =
          case formatting of
              NONE => raw_value
            | SOME (format_context, formats) => format_fun
                (format_term_type_for_name format_context formats special_funs
                  nickname lhs) raw_value
      in
        if MFNT.is_skolem_name name then
          ((cert_evals,
            (MFN.original_name nickname, private_value) :: cert_skolems,
            cert_consts,
            {value = private_value,
             provenance = replay_provenance nickname} :: replay_hints),
           (raw_evals,
            (MFN.original_name nickname, raw_value) :: raw_skolems,
            raw_consts),
           (display_evals,
            (MFN.original_name nickname, display_value) :: display_skolems,
            display_consts))
        else
          case MFN.eval_index nickname of
              SOME index =>
                if index < length eval_terms then
                  let val eval_term = List.nth (eval_terms, index)
                  in
                    (((eval_term, private_value) :: cert_evals,
                      cert_skolems, cert_consts, replay_hints),
                     ((eval_term, raw_value) :: raw_evals,
                      raw_skolems, raw_consts),
                     ((eval_term, formatted_value eval_term raw_value) ::
                        display_evals,
                      display_skolems, display_consts))
                  end
                else
                  ((cert_evals, cert_skolems, cert_consts, replay_hints),
                   (raw_evals, raw_skolems, raw_consts),
                   (display_evals, display_skolems, display_consts))
            | NONE =>
                ((cert_evals, cert_skolems,
                  (lhs, assignment_operator nickname, private_value) ::
                    cert_consts, replay_hints),
                 (raw_evals, raw_skolems,
                  (lhs, assignment_operator nickname, raw_value) ::
                    raw_consts),
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
    val ((cert_evals, cert_skolems, cert_consts, replay_hints),
         (raw_evals, raw_skolems, raw_consts),
         (display_evals, display_skolems, display_consts)) =
      List.foldl classify
        (([], [], [], []), ([], [], []), ([], [], [])) displayed_names

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
    val cert_types = map values_for_type report_types
    val raw_types = map (fn (ty, values, complete) =>
      (ty, map public_value values, complete)) cert_types
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
    val binding_views = map binding real_frees
    val cert_bindings = map #1 binding_views
    val raw_bindings = map #2 binding_views
    val display_bindings = map #3 binding_views
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
      (map process_type raw_types)
    val certification = result cert_bindings cert_evals cert_skolems
      cert_consts cert_types
    val sidecar = sidecar_for (current_holes ()) certification
  in
    {raw = result raw_bindings raw_evals raw_skolems raw_consts raw_types,
     certification = certification,
     displayed =
       (case formatting of
            NONE => result display_bindings display_evals display_skolems
              display_consts raw_types
          | SOME _ => displayed_result ()),
     replay_hints = rev replay_hints,
     replay_sidecar = sidecar,
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

fun model_report ({skolems, consts, types, ...} : reconstruction) =
  {skolems = skolems, consts = consts, types = types}

fun is_unknown term =
  Term.is_var term andalso #1 (Term.dest_var term) = "?"

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

fun valid_replay_sidecar ({holes} : replay_sidecar) =
  let
    fun distinct eq values =
      let
        fun loop _ [] = true
          | loop seen (value :: rest) =
              not (List.exists (eq value) seen) andalso
              loop (value :: seen) rest
      in
        loop [] values
      end
    val ids = map #id holes
    val variables = map #variable holes
  in
    List.all (fn ({id, variable, ...} : replay_hole) =>
      id >= 0 andalso Term.is_var variable andalso
      #1 (Term.dest_var variable) = MFN.replay_hole_name id) holes andalso
    distinct (fn left => fn right => left = right) ids andalso
    distinct (fn left => fn right => Term.aconv left right) variables
  end

(* A qualifying Frac binding is dropped, not authorized: replay does not
   need it in [env], since [closure_of] still quantifies the variable and
   [certification_copy] separately offers the recovered literal as a
   hint.  This keeps "every free variable of an env value is a declared
   hole" true of the returned list without widening it. *)
(* Every free variable of [value] is one of the declared holes.  Both
   the raw bindings and the type-substituted copies below are gated on
   exactly this, so it is stated once. *)
fun bound_by declared value =
  List.all (fn free => Util.aconv_member free declared)
    (Term.free_vars_lr value)

fun certification_env_with_holes (sidecar as {holes}) bindings =
  let
    val declared = map #variable holes
    val authorized = bound_by declared
    fun keep [] = SOME []
      | keep (binding :: rest) =
          if authorized (#2 binding) then
            Option.map (fn kept => binding :: kept) (keep rest)
          else if qualifying_frac_binding binding then keep rest
          else NONE
  in
    if valid_replay_sidecar sidecar then keep bindings else NONE
  end

fun rf_type card =
  Type.mk_thy_type
    {Thy = "refute", Tyop = "rf" ^ Int.toString card, Args = []}

fun rf_constructor card serial =
  Term.prim_mk_const
    {Thy = "refute", Name = "rf" ^ Int.toString card ^ "_" ^
       Int.toString serial}

(* [frac_terms] derives the untrusted real-literal candidates
   [qualifying_frac_binding] recovers from [bindings]; folded into the same
   [replay_candidate_limit] budget as [replay_hints]/[type_values], so it
   must be computed before that budget is split. *)
fun frac_terms bindings =
  List.mapPartial (fn binding as (_, value) =>
    if qualifying_frac_binding binding then SOME (frac_atom_to_real value)
    else NONE) bindings

fun certification_hint_inputs types replay_hints frac_hints =
  let
    val limit = Refute_Cert_Model.replay_candidate_limit
    val replay_hints = MFS.take_at_most limit replay_hints
    val after_replay = limit - length replay_hints
    val frac_hints = MFS.take_at_most after_replay frac_hints
    val type_values = MFS.take_at_most (after_replay - length frac_hints)
      (List.concat (map #2 types))
  in
    (replay_hints, frac_hints, type_values)
  end

(* Certification is deliberately performed on a private, monomorphic copy.
   A native goal type variable with scope cardinality k is transported to
   the static rf_k enum and its displayed fake atoms are transported to the
   corresponding constructors.  The reconstructed model itself remains
   polymorphic, so none of these rf terms escape into model display. *)
fun certification_copy scope types original eval_terms bindings replay_hints
      (sidecar as {holes}) =
  let
    val (replay_hints, frac_hints, type_values) =
      certification_hint_inputs types replay_hints (frac_terms bindings)
    val hint_values = map #value replay_hints
    val copied_terms =
      original :: eval_terms @
      List.concat (map (fn (left, right) => [left, right]) bindings) @
      hint_values @ type_values
    val tyvars = Lib.U (map Term.type_vars_in_term
      copied_terms)
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
    fun optional_values copy declared values =
      List.mapPartial (fn value =>
        (case Lib.total copy value of
             SOME copied =>
               if bound_by declared copied then SOME copied else NONE
           | NONE => NONE)) values
    fun copy_provenance copy_type provenance =
      Option.map (Refute_Skolem.map_types copy_type) provenance
    (* [frac_hints] terms are already closed ([qualifying_frac_binding]
       requires no free variables) and already budget-capped by
       [certification_hint_inputs], so unlike [copied_hints]/[copied_types]
       they need neither a [copy]/[declared] check nor [copy_type]. *)
    val frac_hint_records = map (fn term =>
      {term = term, source = Refute_Cert_Model.DirectHint,
       provenance = NONE}) frac_hints
    fun finish copied_original copied_evals env copied_holes copy copy_type =
      let
        val initial = map #2 env
        val declared = map #variable copied_holes
        val copied_hints = List.mapPartial (fn
          ({value, provenance, ...} : replay_hint) =>
            case Lib.total copy value of
                SOME copied =>
                  if bound_by declared copied then
                    SOME
                      {term = copied,
                       source = Refute_Cert_Model.SkolemValue,
                       provenance = copy_provenance copy_type provenance}
                  else NONE
              | NONE => NONE) replay_hints
        val copied_types = map (fn value =>
          {term = value,
           source = Refute_Cert_Model.TypeValue,
           provenance = NONE}) (optional_values copy declared type_values)
        fun already_seen term accumulated =
          Util.aconv_member term initial orelse
          List.exists (fn
            ({term = old, ...} : Refute_Cert_Model.replay_hint) =>
              Term.aconv old term) accumulated
        fun add_unique
              (hint as {term, ...} : Refute_Cert_Model.replay_hint,
               accumulated) =
          if already_seen term accumulated then accumulated
          else hint :: accumulated
        val hints = rev (List.foldl add_unique []
          (copied_hints @ copied_types @ frac_hint_records))
      in
        SOME
          {original = copied_original, eval_terms = copied_evals,
           env = env, hints = hints, holes = declared}
      end
    fun control_has_hole tm = List.exists (fn ({variable, ...} : replay_hole) =>
      Term.free_in variable tm) holes
    val sidecar_admissible =
      valid_replay_sidecar sidecar andalso
      not (control_has_hole original) andalso
      List.all (not o control_has_hole) eval_terms andalso
      List.all (not o control_has_hole o #1) bindings
  in
    if not sidecar_admissible then NONE
    else if null tyvars then
      (case certification_env_with_holes sidecar bindings of
           SOME env => finish original eval_terms env holes (fn value => value)
             (fn ty => ty)
         | NONE => NONE)
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
                      val avoids =
                        List.concat (map Term.all_vars copied_terms) @
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
                        (Term.inst theta (Term.subst source_atoms value))
                      val env = map (fn (variable, value) =>
                        (Term.inst theta variable, copy_value value)) bindings
                      val copied_holes = map (fn
                        ({id, variable, display, origin} : replay_hole) =>
                          {id = id, variable = copy_value variable,
                           display = display, origin = origin}) holes
                      val copied_sidecar = {holes = copied_holes}
                    in
                      case certification_env_with_holes copied_sidecar env of
                          SOME filtered_env =>
                            finish (Term.inst theta original)
                              (map (Term.inst theta) eval_terms) filtered_env
                              copied_holes copy_value (Type.type_subst theta)
                        | NONE => NONE
                    end
            end
  end

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
             reconstruction = reconstructed,
             certification = private_reconstruction, replay_sidecar,
             replay_hints, cex, sound,
             genuine_means_genuine = genuine, reasons, deadline} =
  let
    val {bindings, evals, codatatypes_ok, ...} = reconstructed
    val {bindings = private_bindings, types = private_types,
         codatatypes_ok = private_codatatypes_ok, ...} =
      private_reconstruction
    val genuine = genuine andalso codatatypes_ok
    val model = SOME (model_report reconstructed)
    val base = replace_cex cex (fallback_certainty sound genuine reasons)
      bindings evals NONE model
  in
    case if executable andalso codatatypes_ok andalso
            private_codatatypes_ok then
           certification_copy (#scope cex) private_types original eval_terms
             private_bindings replay_hints replay_sidecar
         else NONE of
        NONE => Keep base
      | SOME {original = cert_original, eval_terms = cert_evals,
              env, hints, holes} =>
          let
            val (replay, replay_diagnostics) =
              Refute_Cert_Model.certify_portfolio_detailed_rich
                {original = cert_original, env = env, hints = hints,
                 holes = holes,
                 policy = Refute_Cert_Model.default_policy 10000,
                 deadline = deadline}
            fun trace_candidates () =
              let
                val candidates = #candidate_trace replay_diagnostics
                val shown = if length candidates <= 16 then candidates
                  else List.take (candidates, 16)
                val suffix = if length candidates <= 16 then ""
                  else ", ..."
              in
                HOL_MESG ("Refute model replay candidates: " ^
                  String.concatWith ", " (map (fn (_, candidate, _) =>
                    Parse.term_to_string candidate) shown) ^ suffix)
              end
            fun trace_attempts () =
              let
                val sidecar_holes = #holes replay_sidecar
                fun count origin = length (List.filter (fn
                  ({origin = actual, ...} : replay_hole) =>
                    actual = origin) sidecar_holes)
                fun row (label, origin) =
                  label ^ "=" ^ Int.toString (count origin)
                val origins =
                  [("any", AnyRepresentation),
                   ("optional", OptionalAbsent),
                   ("function-fallback", IncompleteFunctionFallback),
                   ("function-point", UnknownFunctionPoint),
                   ("set-membership", PartialSetMembership),
                   ("set-unrepresented", UnrepresentedSetElement),
                   ("function-default", FunctionDefault)]
              in
                HOL_MESG ("Refute model replay attempts: schematic=" ^
                  Int.toString (#schematic_attempts replay_diagnostics) ^
                  ", completions=" ^
                  Int.toString (#completion_attempts replay_diagnostics) ^
                  ", holes={" ^
                  String.concatWith ", " (map row origins) ^ "}")
              end
            val _ = if current_trace "Refute" >= 2 then trace_attempts ()
              else ()
          in
          (case replay of
             Refute_Cert_Model.Certified certificate =>
                 (* A genuine result may display only values established by
                    the kernel certificate.  Decoded solver values are
                    useful reconstruction data, but are not certificates. *)
                 if List.exists (fn hole =>
                      List.exists (Term.free_in hole)
                        (Thm.concl certificate :: Thm.hyp certificate)) holes
                 then Keep base
                 else
                   let
                     val _ = MFN.assert_no_reserved_in_theorem
                       "model replay" certificate
                     fun source_skolem_binding
                           ({term,
                             source = Refute_Cert_Model.SkolemValue,
                             provenance = SOME
                               {origin = SOME _, source_name, source_type,
                                dependencies = [], arity = 0, ...}}
                            : Refute_Cert_Model.replay_hint) =
                           if Util.same_type source_type (Term.type_of term)
                           then SOME
                             (Term.mk_var (source_name, source_type), term)
                           else NONE
                       | source_skolem_binding _ = NONE
                     fun add_binding
                           (binding as (variable, _), bindings) =
                       if List.exists (fn (old, _) =>
                            Term.aconv old variable) bindings
                       then bindings
                       else bindings @ [binding]
                     (* Equation-side evaluation terms are formed after
                        outer universal binders have been opened.  Replay
                        knows their certified values as zero-arity Skolem
                        hints, so restore that source-variable environment.
                        Ambiguous source binders have no origin and are
                        deliberately excluded by the pattern above. *)
                     val eval_env = List.foldl add_binding env
                       (List.mapPartial source_skolem_binding hints)
                     (* Only kernel-established values are shown: any
                        remaining free variable - a replay hole, or an
                        ordinary variable left over from a dropped
                        binding (e.g. a qualifying real Frac atom) - means
                        [tm] was not actually reduced, so the row is
                        dropped rather than displayed half-evaluated. *)
                     fun safe_eval tm =
                       let val value = Refute_Cert.eval_term eval_env tm
                       in
                         if null (Term.free_vars_lr value)
                         then SOME (tm, value)
                         else NONE
                       end
                     val values = List.mapPartial safe_eval cert_evals
                   in
                     Keep (replace_cex base Refute_Core.Genuine bindings
                       values (SOME certificate) NONE)
                   end
             | Refute_Cert_Model.NoCertificate reason =>
                 let
                   val _ = if current_trace "Refute" >= 2 then
                       (HOL_MESG ("Refute model replay: " ^ reason);
                        trace_candidates ())
                     else ()
                 in
                 (case #certainty base of
                      Refute_Core.Genuine => Keep base
                    | Refute_Core.QuasiGenuine _ => Keep base
                    | Refute_Core.Potential encoding_reasons =>
                        Keep (replace_cex base
                          (Refute_Core.Potential
                            (encoding_reasons @ [reason]))
                          bindings evals NONE model))
                 end
             | Refute_Cert_Model.DiscardedByWholeFormulaEval =>
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

end
