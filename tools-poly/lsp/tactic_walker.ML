(* Interpret a TacticParse.tac_frag list against a starting
   goalFrag.goalstate, applying each fragment and returning the
   state at the cursor's fragment index.  Snapshots each successful
   FAtom's post-state into a per-theorem cache stored in
   plugin_data, so subsequent queries in the same theorem resume
   from the closest snapshot rather than re-walking. *)

structure TacticWalker :> sig
  (* Exposed because PolyML.compiler compiles at top level: `holder`
     must be reachable by qualified name from the wrapped
     `TacticWalker.holder := SOME (…)` source that compileTactic
     runs.  Not part of the public API. *)
  val holder : Abbrev.tactic option ref

  val walkTo : {
    plugins: LSPExtension.plugin_data,
    theoremName: string,
    theoremStart: int,   (* file byte offset of the theorem's dec *)
    tacText: string,
    startState: goalFrag.goalstate,
    frags: TacticParse.tac_frag list,
    cursor: int
  } -> { state: goalFrag.goalstate,
         failedAt: TacticParse.tac_frag option }
end = struct

open TacticParse

val holder : Abbrev.tactic option ref = ref NONE

(* Process-lifetime cache of compiled tactic values, keyed by their
   source text.  Per-atom PolyML.compiler invocation dominates
   walker cost — the point of `hol-lsp-goals-follow-cursor` is that
   auto-follow keystrokes should feel snappy. *)
val compileCache: (string, Abbrev.tactic) Binarymap.dict ref =
  ref (Binarymap.mkDict String.compare)

fun compileTactic src =
  case Binarymap.peek (!compileCache, src) of
    SOME tac => SOME tac
  | NONE => let
      val wrapped = "TacticWalker.holder := SOME (" ^ src ^ ");"
      val filtered = HOLSource.fromString
                       {quietOpen = true, print = fn _ => ()} wrapped
      val i = ref 0
      val n = String.size filtered
      fun read () = if !i >= n then NONE
                    else SOME (String.sub (filtered, !i)) before i := !i + 1
      fun swallow _ = ()
      val () = holder := NONE
      val _ = Portable.total (fn () => PolyML.compiler
                 (read, [PolyML.Compiler.CPErrorMessageProc swallow,
                         PolyML.Compiler.CPPrintStream swallow,
                         PolyML.Compiler.CPOutStream swallow,
                         PolyML.Compiler.CPNameSpace LSPNameSpace.fileNS]) ()) ()
      val () = case !holder of
                 SOME tac => compileCache :=
                             Binarymap.insert (!compileCache, src, tac)
               | NONE => ()
      in !holder end

fun compileAndApply src state =
  case compileTactic src of
    NONE => NONE
  | SOME tac => Portable.total (goalFrag.expand tac) state

fun textAt tacText (s, e) = String.substring (tacText, s, e - s)

(* The source to compile for a leaf, or NONE for one that is a
   no-op.  The four sugars name their entry point in full because
   their spans cover a quotation rather than a tactic, and because
   `TacticParse's rendering of them is surface syntax needing
   particular opens: `sg' from bossLib, `SELECT_GOAL_LT' and
   `RENAME_TAC' from Q.  Leaves carrying a whole-expression span use
   that source verbatim.  Anything left goes back through
   `TacticParse's inverse printer, which is what keeps `applyAtom'
   total -- a leaf kind nobody anticipated still applies rather than
   halting the walk at the previous step.  Every name reachable that
   way (MAP_EVERY, NO_TAC, TACS_TO_LT, REVERSE_LT, ...) lives in
   Tactical, so it needs no opens.

   The `>>>' wrapper for a list_tactic is there because
   `compileTactic' is typed through a single tactic-valued `holder';
   `goalFrag.expand_list' would take one more ref and a twin
   compile. *)
fun atomSrc tacText te = let
  val txt = textAt tacText
  in case te of
      Subgoal span      => SOME ("BasicProvers.subgoal " ^ txt span)
    | LSelectGoal span  => SOME ("ALL_TAC >~ [" ^ txt span ^ "]")
    | LSelectGoals span => SOME ("ALL_TAC >>~ [" ^ txt span ^ "]")
    | Rename span       => SOME ("Q.RENAME_TAC " ^ txt span)
    | _ => case topSpan te of
        SOME span => SOME (txt span)
      | NONE => Option.map
          (fn src => if isTac te then src
                     else "ALL_TAC >>> (" ^ src ^ ")")
          (printTacAsSML tacText te)
  end

fun applyAtom tacText te state = case atomSrc tacText te of
    NONE => SOME state
  | SOME src => compileAndApply src state

fun applyOpen ok state = case ok of
    FOpen           => Portable.total goalFrag.open_paren      state
  | FOpenThen1      => Portable.total goalFrag.open_then1      state
  | FOpenFirst      => Portable.total goalFrag.open_first      state
  | FOpenRepeat     => Portable.total goalFrag.open_repeat     state
  | FOpenTacsToLT   => Portable.total goalFrag.open_tacs_to_lt state
  | FOpenNullOk     => Portable.total goalFrag.open_null_ok    state
  | FOpenNthGoal (n, _) => Portable.total (goalFrag.open_nth_goal n) state
  | FOpenLastGoal   => Portable.total goalFrag.open_last_goal  state
  | FOpenHeadGoal   => Portable.total goalFrag.open_head_goal  state
  | FOpenSplit (n, _) => Portable.total (goalFrag.open_split_lt n) state
  | FOpenSelect     => Portable.total goalFrag.open_select_lt  state
  | FOpenFirstLT    => Portable.total goalFrag.open_first_lt   state

fun applyMid m state = case m of
    FNextFirst    => Portable.total goalFrag.next_first     state
  | FNextTacsToLT => Portable.total goalFrag.next_tacs_to_lt state
  | FNextSplit    => Portable.total goalFrag.next_split_lt  state
  | FNextSelect   => Portable.total goalFrag.next_select_lt state

fun applyClose c state = case c of
    FClose        => Portable.total goalFrag.close_paren    state
  | FCloseFirst   => Portable.total goalFrag.close_first    state
  | FCloseRepeat  => Portable.total goalFrag.close_repeat   state
  | FCloseFirstLT => Portable.total goalFrag.close_first_lt state

val atomEndByte = TacticSteps.atomEndByte

fun fragEnd frag = case frag of
    FAtom te => atomEndByte te
  | FGroup ((_, e), _) => SOME e
  | FBracket (_, inner, _, te) =>
      bracketEndByte te (fn () => lastFragEnd inner)
  | FMBracket (_, _, _, sections, te) => bracketEndByte te (fn () =>
      lastSectionEnd sections)
  | FFOpen _ | FFMid _ | FFClose _ => NONE

(* Rightmost fragment span in a list -- foldl walking L-R and
   keeping the last SOME.  Fragments are in source order, so this
   is the maximum end position without a `List.rev`. *)
and lastFragEnd frags =
  List.foldl (fn (f, acc) => case fragEnd f of NONE => acc | some => some)
             NONE frags

and lastSectionEnd sections =
  List.foldl (fn (s, acc) => case lastFragEnd s of NONE => acc | some => some)
             NONE sections

(* `lastInner' is a thunk because it is only wanted for a wrapper
   whose own span is missing, as `LThen1's and `Try's are. *)
and bracketEndByte te lastInner = case topSpan te of
    SOME (_, e) => SOME e
  | NONE => (case atomEndByte te of
      SOME e => SOME e
    | NONE => lastInner ())

type snap = {stepIdx: int, endByte: int, state: goalFrag.goalstate}
type cacheEntry = {
  tacText: string,
  theoremStart: int,
  snapshots: snap list}
type cacheMap = (string, cacheEntry) Binarymap.dict
type cacheData = cacheMap ref

val latestCacheRef : cacheData option ref = ref NONE

val cacheTag : cacheData LSPExtension.tag =
  LSPExtension.registerPlugin false {
    name = "goalStateCache",
    init = fn _ => (),
    beforeCompile = fn () => (),
    afterCompile = fn (_, prev) => let
      val r = case prev of
                SOME r => r
              | NONE => ref (Binarymap.mkDict String.compare)
      val () = latestCacheRef := SOME r
    in SOME r end
  }

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
         r := Binarymap.mkDict String.compare
     | (NONE, _) => ());
    prev minEdit))
end

fun bestSnap cursor =
  List.foldl
    (fn (s, acc) =>
      if #endByte s > cursor then acc
      else case acc of
             NONE => SOME s
           | SOME s' => if #endByte s > #endByte s' then SOME s else acc)
    NONE

fun commonPrefixLen (a, b) = let
  val n = Int.min (String.size a, String.size b)
  fun go i = if i >= n orelse String.sub (a, i) <> String.sub (b, i) then i
             else go (i + 1)
  in go 0 end

fun resumeFrom NONE _ startState = (0, startState, [])
  | resumeFrom (SOME cacheRef) {theoremName, tacText, cursor} startState =
      case Binarymap.peek (!cacheRef, theoremName) of
        NONE => (0, startState, [])
      | SOME {tacText = t, snapshots, ...} => let
          val validUpTo = if t = tacText then String.size t
                          else commonPrefixLen (t, tacText)
          val kept = List.filter (fn s => #endByte s <= validUpTo) snapshots
          in case bestSnap cursor kept of
               NONE => (0, startState, kept)
             | SOME {stepIdx, state, ...} =>
                 (stepIdx + 1, state, kept)
          end

datatype walkOut =
  Done of {state: goalFrag.goalstate, snaps: snap list, stepIdx: int}
| Halted of {state: goalFrag.goalstate, snaps: snap list, stepIdx: int}
| Failed of {state: goalFrag.goalstate, snaps: snap list, stepIdx: int,
             at: tac_frag}

fun walkFrag tacText cursor state snaps stepIdx frag = case frag of
    FAtom te => (case atomEndByte te of
        SOME endB =>
          if cursor < endB then
            Halted {state = state, snaps = snaps, stepIdx = stepIdx}
          else (case applyAtom tacText te state of
                  NONE => Failed {state = state, snaps = snaps,
                                  stepIdx = stepIdx, at = frag}
                | SOME state' =>
                    Done {state = state',
                          snaps = {stepIdx = stepIdx, endByte = endB,
                                   state = state'} :: snaps,
                          stepIdx = stepIdx + 1})
      | NONE => (* no snap key: apply as an always-fires leaf (e.g. LReverse) *)
          (case applyAtom tacText te state of
             NONE => Failed {state = state, snaps = snaps,
                             stepIdx = stepIdx, at = frag}
           | SOME state' =>
               Done {state = state', snaps = snaps, stepIdx = stepIdx}))
  | FFOpen ok =>
      (case applyOpen ok state of
         NONE => Failed {state = state, snaps = snaps,
                         stepIdx = stepIdx, at = frag}
       | SOME state' =>
           Done {state = state', snaps = snaps, stepIdx = stepIdx})
  | FFMid m =>
      (case applyMid m state of
         NONE => Failed {state = state, snaps = snaps,
                         stepIdx = stepIdx, at = frag}
       | SOME state' =>
           Done {state = state', snaps = snaps, stepIdx = stepIdx})
  | FFClose c =>
      (case applyClose c state of
         NONE => Failed {state = state, snaps = snaps,
                         stepIdx = stepIdx, at = frag}
       | SOME state' =>
           Done {state = state', snaps = snaps, stepIdx = stepIdx})
  | FGroup (_, inner) =>
      walkFrags tacText cursor state snaps stepIdx inner
  (* Transparent bracket: `open_null_ok`'s Parallel frame would
     hide the inner TacsToLT context from `pp_goalstate`. *)
  | FBracket (FOpenNullOk, inner, _, _) =>
      walkFrags tacText cursor state snaps stepIdx inner
  | FBracket (ok, inner, cc, te) =>
      (case bracketEndByte te (fn () => lastFragEnd inner) of
        SOME be =>
          if cursor < be then
            (* Open, walk inner as far as cursor lets us; don't close. *)
            (case applyOpen ok state of
               NONE => Failed {state = state, snaps = snaps,
                               stepIdx = stepIdx, at = FFOpen ok}
             | SOME state' =>
                 (case walkFrags tacText cursor state' snaps stepIdx inner of
                    Done r =>
                      Halted {state = #state r, snaps = #snaps r,
                              stepIdx = #stepIdx r}
                  | Halted r => Halted r
                  | Failed r => Failed r))
        else
          (* Cursor past the whole bracket: open + walk + close. *)
          (case applyOpen ok state of
             NONE => Failed {state = state, snaps = snaps,
                             stepIdx = stepIdx, at = FFOpen ok}
           | SOME state' =>
               (case walkFrags tacText cursor state' snaps stepIdx inner of
                  Failed r => Failed r
                | Halted r => Halted r
                | Done r =>
                    (case applyClose cc (#state r) of
                       NONE => Failed {state = #state r, snaps = #snaps r,
                                       stepIdx = #stepIdx r, at = FFClose cc}
                     | SOME state'' =>
                         Done {state = state'', snaps = #snaps r,
                               stepIdx = #stepIdx r})))
      | NONE => (* no end position: bail as opaque *)
          Failed {state = state, snaps = snaps,
                  stepIdx = stepIdx, at = frag})
  | FMBracket (ok, mid, cc, sections, te) =>
      (case bracketEndByte te (fn () => lastSectionEnd sections) of
        SOME be =>
          let
            (* `walkFrags` returns Done only when it has walked
               every frag in a section — i.e., cursor sits after
               the section's last atom.  In that state we can
               safely advance to the next section via `applyMid`.
               A cursor inside the current section short-circuits
               with Halted, which propagates immediately. *)
            fun walkSections state snaps stepIdx sections =
              case sections of
                [] => Done {state = state, snaps = snaps, stepIdx = stepIdx}
              | [sec] => walkFrags tacText cursor state snaps stepIdx sec
              | sec :: rest =>
                  (case walkFrags tacText cursor state snaps stepIdx sec of
                     Done r =>
                       (case applyMid mid (#state r) of
                          NONE => Failed {state = #state r,
                                          snaps = #snaps r,
                                          stepIdx = #stepIdx r,
                                          at = FFMid mid}
                        | SOME state' =>
                            walkSections state' (#snaps r)
                                         (#stepIdx r) rest)
                   | Halted r => Halted r
                   | Failed r => Failed r)
          in
            if cursor < be then
              (case applyOpen ok state of
                 NONE => Failed {state = state, snaps = snaps,
                                 stepIdx = stepIdx, at = FFOpen ok}
               | SOME state' =>
                   (case walkSections state' snaps stepIdx sections of
                      Done r => Halted {state = #state r, snaps = #snaps r,
                                        stepIdx = #stepIdx r}
                    | Halted r => Halted r
                    | Failed r => Failed r))
            else
              (case applyOpen ok state of
                 NONE => Failed {state = state, snaps = snaps,
                                 stepIdx = stepIdx, at = FFOpen ok}
               | SOME state' =>
                   (case walkSections state' snaps stepIdx sections of
                      Done r =>
                        (case applyClose cc (#state r) of
                           NONE => Failed {state = #state r,
                                           snaps = #snaps r,
                                           stepIdx = #stepIdx r,
                                           at = FFClose cc}
                         | SOME state'' =>
                             Done {state = state'', snaps = #snaps r,
                                   stepIdx = #stepIdx r})
                    | Halted r => Halted r
                    | Failed r => Failed r))
          end
      | NONE => Failed {state = state, snaps = snaps,
                        stepIdx = stepIdx, at = frag})

and walkFrags tacText cursor state snaps stepIdx frags = case frags of
    [] => Done {state = state, snaps = snaps, stepIdx = stepIdx}
  | f :: rest =>
      (case walkFrag tacText cursor state snaps stepIdx f of
         Done r =>
           walkFrags tacText cursor (#state r) (#snaps r) (#stepIdx r) rest
       | Halted r => Halted r
       | Failed r => Failed r)

(* Skip forward through frags until stepIdx reaches resumeIdx.
   The resume state already reflects the pre-cursor atoms; only
   structural markers need re-firing to reach that state. *)
fun advanceToResume resumeIdx state stepIdx frags = let
  fun consume [] state stepIdx = ([], state, stepIdx)
    | consume (fs as (f :: rest)) state stepIdx =
        if stepIdx >= resumeIdx then (fs, state, stepIdx)
        else case f of
          FAtom _ =>
            consume rest state (stepIdx + 1)
        | FFOpen ok =>
            (case applyOpen ok state of
               NONE => (fs, state, stepIdx)
             | SOME s' => consume rest s' stepIdx)
        | FFMid m =>
            (case applyMid m state of
               NONE => (fs, state, stepIdx)
             | SOME s' => consume rest s' stepIdx)
        | FFClose c =>
            (case applyClose c state of
               NONE => (fs, state, stepIdx)
             | SOME s' => consume rest s' stepIdx)
        | _ => (fs, state, stepIdx)  (* nested; fall through to full walk *)
  in consume frags state stepIdx end

fun walkTo {plugins, theoremName, theoremStart, tacText, startState,
            frags, cursor} = let
  val cacheRefOpt = LSPExtension.getPluginData (plugins, cacheTag)
  val (resumeIdx, resumeState, priorSnaps) =
    resumeFrom cacheRefOpt
      {theoremName = theoremName, tacText = tacText, cursor = cursor}
      startState
  val (frags', state', stepIdx') =
    if resumeIdx = 0 then (frags, resumeState, 0)
    else let val (fs, s, i) = advanceToResume resumeIdx resumeState 0 frags
         (* Only trust the resume if we could step to it via flat
            markers.  A cache miss inside a bracket restarts from
            startState, else we'd re-apply cached atoms. *)
         in if i >= resumeIdx then (fs, s, i) else (frags, startState, 0)
         end
  val outcome = walkFrags tacText cursor state' priorSnaps stepIdx' frags'
                handle Portable.Interrupt =>
                  Halted {state = state', snaps = priorSnaps,
                          stepIdx = stepIdx'}
  val (finalState, allSnaps, failedAt) = case outcome of
      Done r    => (#state r, #snaps r, NONE)
    | Halted r  => (#state r, #snaps r, NONE)
    | Failed r  => (#state r, #snaps r, SOME (#at r))
  val _ = case (cacheRefOpt, allSnaps) of
      (SOME cacheRef, _ :: _) => let
        val deduped = Lib.op_mk_set
                        (fn s1 => fn s2 => #stepIdx s1 = #stepIdx s2)
                        allSnaps
        in cacheRef := Binarymap.insert
                         (!cacheRef, theoremName,
                          {tacText = tacText, theoremStart = theoremStart,
                           snapshots = deduped})
        end
    | _ => ()
  in {state = finalState, failedAt = failedAt} end

end;
