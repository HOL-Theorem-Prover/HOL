(* Interpret a TacticSteps.step stream against a starting
   goalFrag.goalstate, applying each step and returning the state at
   the cursor's step index.  Snapshots each Expand's post-state into a
   per-theorem cache stored in plugin_data, so subsequent queries in
   the same theorem resume from the closest snapshot rather than
   re-walking. *)

structure TacticWalker :> sig
  (* Exposed because PolyML.compiler compiles at top level: `holder`
     must be reachable by qualified name from the wrapped
     `TacticWalker.holder := SOME (…)` source that compileTactic
     runs.  Not part of the public API — callers should treat this
     as private. *)
  val holder : Abbrev.tactic option ref

  (* Applies steps in order.  For Expand/ExpandList steps whose end
     byte is > cursor, stops BEFORE applying — the "pre-state of the
     step under the cursor".  Markers (Open/Close) are always applied
     when reached.  Halts on the first step that fails to compile or
     apply, returning the last successful state.

     Cache invalidation is implicit: an entry with a different
     `tacText` for the same theorem is replaced on the next walk. *)
  val walkTo : {
    plugins: LSPExtension.plugin_data,
    theoremName: string,
    theoremStart: int,   (* file byte offset of the theorem's dec *)
    tacText: string,
    startState: goalFrag.goalstate,
    steps: TacticSteps.step list,
    cursor: int
  } -> goalFrag.goalstate
end = struct

val holder : Abbrev.tactic option ref = ref NONE

fun compileTactic src = let
  val wrapped = "TacticWalker.holder := SOME (" ^ src ^ ");"
  (* Run the HOL quotation filter over the wrapped source: backticks
     become `[QUOTE …]`, so tactics like `Cases_on \`p\`` reach
     PolyML in the form it can parse.  Same pipeline the LSP file
     compile uses. *)
  val filtered = HOLSource.fromString
                   {quietOpen = true, print = fn _ => ()} wrapped
  val i = ref 0
  val n = String.size filtered
  fun read () = if !i >= n then NONE
                else SOME (String.sub (filtered, !i)) before i := !i + 1
  fun swallow _ = ()
  val () = holder := NONE
  (* Resolve identifiers via the LSP's file namespace layer, same
     layer the LSP's normal compile uses, so identifiers visible to
     hover are visible here.  Swallow PolyML's own output streams so
     the `val it = () : unit` chatter doesn't leak onto the LSP
     server's stderr for every step. *)
  val _ = Portable.total (fn () => PolyML.compiler
             (read, [PolyML.Compiler.CPErrorMessageProc swallow,
                     PolyML.Compiler.CPPrintStream swallow,
                     PolyML.Compiler.CPOutStream swallow,
                     PolyML.Compiler.CPNameSpace LSPNameSpace.fileNS]) ()) ()
  in !holder end

fun expandSpan (TacticSteps.Expand span)     = SOME span
  | expandSpan (TacticSteps.ExpandList span) = SOME span
  | expandSpan _                             = NONE

fun expandSrc tacText (s, e) state =
  case compileTactic (String.substring (tacText, s, e - s)) of
    NONE => NONE
  | SOME tac => Portable.total (goalFrag.expand tac) state

fun applyStep tacText step state = case expandSpan step of
    SOME span => expandSrc tacText span state
  | NONE => (case step of
      TacticSteps.OpenParen _   => Portable.total goalFrag.open_paren   state
    | TacticSteps.CloseParen _  => Portable.total goalFrag.close_paren  state
    | TacticSteps.OpenThen1 _   => Portable.total goalFrag.open_then1   state
    | TacticSteps.OpenFirst _   => Portable.total goalFrag.open_first   state
    | TacticSteps.NextFirst _   => Portable.total goalFrag.next_first   state
    | TacticSteps.CloseFirst _  => Portable.total goalFrag.close_first  state
    | TacticSteps.OpenRepeat _  => Portable.total goalFrag.open_repeat  state
    | TacticSteps.CloseRepeat _ => Portable.total goalFrag.close_repeat state
    | TacticSteps.OpenNthGoal (n, _) =>
        Portable.total (goalFrag.open_nth_goal n) state
    | _ => SOME state)

type snap = {stepIdx: int, endByte: int, state: goalFrag.goalstate}
type cacheEntry = {
  tacText: string,
  theoremStart: int,  (* file byte offset where the theorem's dec begins *)
  snapshots: snap list}
type cacheMap = (string, cacheEntry) Binarymap.dict
type cacheData = cacheMap ref

(* Alias to the currently-active cache ref, set by `afterCompile`.
   Used by the `resetForCompile` wrapping below so we can empty the
   cache at compile-start without going through plugin_data (which
   isn't accessible from that hook). *)
val latestCacheRef : cacheData option ref = ref NONE

val cacheTag : cacheData LSPExtension.tag =
  LSPExtension.registerPlugin false {
    name = "goalStateCache",
    init = fn _ => (),
    beforeCompile = fn () => (),
    (* Reuse the same ref across compiles so cache entries can survive
       (they're invalidated by tacText comparison at query time).
       Also alias the ref to a module-global so `resetForCompile` can
       reach it. *)
    afterCompile = fn (_, prev) => let
      val r = case prev of
                SOME r => r
              | NONE => ref (Binarymap.mkDict String.compare)
      val () = latestCacheRef := SOME r
    in SOME r end
  }

(* Chain into `notifyCompileStart` — fires at compile-start with the
   buffer's `minEditOffset`.  Cache entries whose theorem begins at
   or after the edit are downstream of the change and may reference a
   stale HOL Context; drop them.  Entries strictly before the edit
   are still valid — their Context is inherited from the snapshot or
   from the unchanged file prefix, so their cached snapshots are
   safe to reuse. *)
val () = let val prev = !LSPExtension.notifyCompileStart in
  LSPExtension.notifyCompileStart := (fn minEdit => (
    (case (!latestCacheRef, minEdit) of
       (SOME r, SOME edit) =>
         r := Binarymap.foldl
                (fn (name, entry, m) =>
                  if #theoremStart entry >= edit then m
                  else Binarymap.insert (m, name, entry))
                (Binarymap.mkDict String.compare) (!r)
     | (SOME r, NONE) =>
         (* No pending edit but a compile is starting: full-file
            didOpen or a manual re-compile.  Safest to drop all. *)
         r := Binarymap.mkDict String.compare
     | (NONE, _) => ());
    prev minEdit))
end

(* Largest snapshot whose endByte ≤ cursor. *)
fun bestSnap cursor =
  List.foldl
    (fn (s, acc) =>
      if #endByte s > cursor then acc
      else case acc of
             NONE => SOME s
           | SOME s' => if #endByte s > #endByte s' then SOME s else acc)
    NONE

fun resumeFrom NONE _ startState = (0, startState, [])
  | resumeFrom (SOME cacheRef) {theoremName, tacText, cursor} startState =
      case Binarymap.peek (!cacheRef, theoremName) of
        NONE => (0, startState, [])
      | SOME {tacText = t, snapshots, ...} =>
          if t <> tacText then (0, startState, [])
          else case bestSnap cursor snapshots of
                 NONE => (0, startState, snapshots)
               | SOME {stepIdx, state, ...} =>
                   (stepIdx + 1, state, snapshots)

fun walkTo {plugins, theoremName, theoremStart, tacText, startState,
            steps, cursor} = let
  val cacheRefOpt = LSPExtension.getPluginData (plugins, cacheTag)
  val (resumeIdx, resumeState, priorSnaps) =
    resumeFrom cacheRefOpt
      {theoremName = theoremName, tacText = tacText, cursor = cursor}
      startState
  (* Walker halts before applying a step whose stopPos is past the
     cursor.  For Expand this is the end of the span; for markers
     like OpenThen1 it is the position of the `>-` operator, so a
     cursor between `EQ_TAC` and `>-` keeps both subgoals visible. *)
  fun stopAt step = cursor < TacticSteps.stopPos step
  fun snapOf idx step newState =
    Option.map (fn (_, e) => {stepIdx = idx, endByte = e, state = newState})
               (expandSpan step)
  fun collect [] _ state acc = (state, acc)
    | collect (step :: rest) idx state acc =
        if idx < resumeIdx then collect rest (idx + 1) state acc
        else if stopAt step then (state, acc)
        else (case applyStep tacText step state of
                NONE => (state, acc)
              | SOME newState =>
                let val acc' = case snapOf idx step newState of
                                 NONE => acc
                               | SOME s => s :: acc
                in collect rest (idx + 1) newState acc' end)
             (* Wall-clock budget from `goal_state_init.ML` interrupts
                this thread when a tactic (typically METIS_TAC) exceeds
                the budget.  Treat the interrupt like a failed step:
                halt with the pre-step state, cache what we already
                walked, and let the caller return partial state. *)
             handle Portable.Interrupt => (state, acc)
  val (finalState, newSnaps) = collect steps 0 resumeState []
  val _ = case (cacheRefOpt, newSnaps) of
      (SOME cacheRef, _::_) => let
        (* Merge new snapshots into the cache, deduping by stepIdx so
           a resumed walk that re-walks past an already-cached step
           replaces rather than duplicates. *)
        val merged = newSnaps @ priorSnaps
        val deduped = Lib.op_mk_set
                        (fn s1 => fn s2 => #stepIdx s1 = #stepIdx s2)
                        merged
      in cacheRef := Binarymap.insert
                       (!cacheRef, theoremName,
                        {tacText = tacText, theoremStart = theoremStart,
                         snapshots = deduped})
      end
    | _ => ()  (* no cache slot yet, or nothing new to store *)
  in finalState end

end;
