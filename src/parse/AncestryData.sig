signature AncestryData =
sig
  type ('delta,'value) adata_info = {
    tag : string, initial_values : (string * 'value) list,
    apply_delta : 'delta -> 'value -> 'value
  }

  type ('delta,'value) fullresult =
       { merge : string list -> 'value option,
         DB : {thyname : string} -> 'value option,
         get_deltas : {thyname : string} -> 'delta list,
         record_delta : 'delta -> unit,
         parents : {thyname : string} -> string list,
         set_parents : string list -> 'value option,
         get_global_value : unit -> 'value,
         update_global_value : ('value -> 'value) -> unit }

  (* doesn't lock, or in any way exclude others from seeing the adjusted
     value while this code is executing *)
  val with_temp_value : ('delta,'value)fullresult -> 'value ->
                        ('a -> 'b) -> ('a -> 'b)


  val make : { info : ('delta, 'value) adata_info,
               get_deltas : {thyname:string} -> 'delta list,
               delta_side_effects : 'delta -> unit } ->
             { merge : string list -> 'value option,
               DB : {thyname : string} -> 'value option,
               parents : {thyname : string} -> string list,
               set_parents : string list -> 'value option
             }

  val fullmake : { adinfo : ('delta, 'value) adata_info,
                   uptodate_delta : 'delta -> bool,
                   sexps : { dec : 'delta ThyDataSexp.dec,
                             enc : 'delta ThyDataSexp.enc },
                   globinfo : {
                     apply_to_global : 'delta -> 'value -> 'value,
                     thy_finaliser : ({thyname:string} -> 'delta list ->
                                      'value -> 'value) option,
                     initial_value : 'value}
                 } ->
                 ('delta,'value) fullresult

end

(* ----------------------------------------------------------------------
    Overview
   ----------------------------------------------------------------------

    AncestryData is a general-purpose mechanism for maintaining a
    persistent value that evolves as theories are brought into the
    current logical context.  When new theories are loaded, the value
    is updated automatically; siblings can independently extend or
    revise it, and merging follows the theory ancestry graph rather
    than asking the user to enumerate state explicitly.  ThmSetData --
    the engine behind [simp], [compute], [rule_induction], [mono],
    the [cv_*] family, and many more attribute-driven theorem
    collections -- is the most visible client; grammar updates,
    TypeBase information, and the src/emit infrastructure persist
    with the same machinery.

    Position in the build.  The module lives in src/parse/ because
    that is the earliest non-kernel directory in the build sequence
    where the abstraction is needed (grammar persistence is the
    earliest user).  The location is largely accidental rather than
    semantic; the file has no parse-related content and could
    plausibly be moved.

    Deltas, not final values.  The central design decision is that a
    theory does not store the *final* value of the persistent
    structure; instead it stores the sequence of *updates* (deltas)
    that produced it.  This matters because two siblings thy1 and
    thy2 may legitimately disagree on the value -- e.g. thy2 may have
    removed a theorem that thy1 added -- so blindly unioning per-
    theory final values is unsafe.  Concatenating delta streams in
    topological order and folding them via apply_delta on a starting
    value is well-defined regardless.

    Module surface.  Two exported types:

      ('delta, 'value) adata_info = {
        tag, initial_values, apply_delta }
        Configuration shared by both constructor functions:
          - tag : a string unique across all AncestryData instances,
            used as the identifier under which deltas are persisted
            (and reused as the attribute name when ThmSetData drives
            the instance, e.g. "simp", "compute").
          - initial_values : a per-theory alist of starting values,
            keyed by theory name.  It is safe to seed this with a
            single ("min", emptyValue) entry for the kernel theory.
          - apply_delta : how a single delta transforms a value.

      ('delta, 'value) fullresult = { merge, DB, get_deltas,
        record_delta, parents, set_parents, get_global_value,
        update_global_value }
        The richer return shape from fullmake.  Callers can:
          - merge thys                : walk the ancestry from the
            given theories, applying their deltas in topological
            order, and return the resulting value (NONE if no
            initial value seeds the calculation).
          - DB {thyname}              : look up the value as it
            stood inside the named theory (built from that theory's
            deltas applied to its parents' value).
          - get_deltas {thyname}      : the raw delta sequence
            stored in a theory.
          - record_delta d            : append a delta to the
            *current* theory's stream and persist it.
          - parents {thyname}         : AncestryData's view of the
            theory's parents.  Normally equals Theory.parents but
            differs if set_parents has been called.
          - set_parents thys          : rewrite the current theory's
            effective parent list (used to graft together ancestries
            that diverge from Theory.parents).
          - get_global_value /
            update_global_value       : access the single mutable
            "global" value -- the one visible to user code via the
            getDB / temp_setDB style API exposed by clients like
            ThmSetData.

    Two constructor functions:

      - make {info, get_deltas, delta_side_effects}
        The simpler of the two.  Used when the caller stores deltas
        elsewhere (e.g. in a separate ThyDataSexp tag they manage
        themselves) and only wants AncestryData to handle the merge
        logic.  Returns the four-field record { merge, DB, parents,
        set_parents }.
      - fullmake {adinfo, uptodate_delta, sexps, globinfo}
        The full-fat version.  Adds:
          - uptodate_delta : called when a theory is loaded to weed
            out deltas whose referenced symbols have been deleted or
            otherwise gone out of date.
          - sexps = {dec, enc} : ThyDataSexp.dec / enc pair used to
            serialise deltas for storage in the theory file.
          - globinfo = {initial_value, apply_to_global,
                        thy_finaliser}
            * initial_value : the starting global value (often the
              same shape as adata_info.initial_values' empty case).
            * apply_to_global : how a delta updates the global --
              normally the same function as adinfo.apply_delta, but
              the split lets clients implement non-monotonic global
              behaviour distinct from per-theory accumulation.
            * thy_finaliser : an optional callback invoked once per
              theory when all of its deltas have been loaded.  Lets
              clients perform per-theory closure work (e.g. compute
              a cached representation) instead of applying deltas
              one at a time.

    Persistence and loading.  Both constructors register themselves
    with Theory.LoadableThyData (see src/postkernel/Theory.sig) under
    derived tag strings:

      - make uses a single ThyDataSexp segment named "<tag>"
        carrying the list of parent names; the actual deltas are
        managed by the caller's get_deltas function.
      - fullmake uses two segments: "<tag>.deltas" (the ThyDataSexp
        encoding of the delta list, augmented by gen_other_tds which
        prunes out-of-date entries on load using uptodate_delta) and
        "<tag>.parents" (the AncestryData parent-list override).

    On theory load, parent_onload reconstructs the theory's value by
    asking the apply_delta_hook (which is bound to merge) to compute
    the value at the parent boundary, then folds in the theory's
    own deltas via apply_delta and stashes the result in
    value_table.  In fullmake, each delta is also fed through
    delta_side_effects, which either applies apply_to_global one
    delta at a time (when no finaliser is supplied) or hands the
    whole batch to thy_finaliser.

    The merge walk.  AncestryData merges multiple ancestor theories
    by:

      1. tts_ancestry "-" : topologically sort the current theory's
         transitive parents, deepest first, using SymGraph and the
         BFS in ImplicitGraph.
      2. purge_redundants : remove theory names from the merge list
         that are already ancestors of another listed theory, so
         each theory's deltas are applied at most once.
      3. Fold apply_delta over the resulting ordered delta sequence,
         seeded by the first listed theory's value.

    The merge function is itself bound as the apply_delta_hook used
    during loading, so the same algorithm computes both the on-load
    state and the value returned by user-visible queries.

    with_temp_value : ('delta,'value)fullresult -> 'value ->
                      ('a -> 'b) -> ('a -> 'b)
    Wraps a function so that during its execution the global value is
    temporarily set to the supplied 'value, with the previous value
    restored on exit (built on Portable.genwith_flag).  There is no
    way to obtain the underlying ref, but get_global_value /
    update_global_value plus with_temp_value let callers simulate one
    when needed -- the slogan from the design talk is "treat it as a
    reference, but only temporarily".

    Relationship to src/postkernel/Theory.  AncestryData layers on
    top of three things from Theory:

      - Theory.parents / Theory.ancestry : the canonical parent
        graph, used as the default before any set_parents override.
      - Theory.LoadableThyData (with ThyDataSexp.new) : per-theory
        persistent data slots.  AncestryData consumes one slot per
        adinfo in make, two in fullmake.
      - Theory's load hooks : parent_onload is invoked when a theory
        is loaded, ensuring that AncestryData's in-memory tables
        track Theory's view of which theories are in scope.

    For most clients the simpler ThmSetData.export_simple_dictionary
    interface (built on top of fullmake) is the right entry point;
    reach for AncestryData directly when the persistent value is
    something more structured than a name-to-theorem dictionary
    (grammars, TypeBase entries, congruence rules, etc.).
   ---------------------------------------------------------------------- *)
