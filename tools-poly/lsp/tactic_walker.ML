(* Interpret a TacticParse.tac_frag list against a starting
   goalFrag.goalstate, applying each fragment and returning the
   state at the cursor's fragment index.  Snapshots each successful
   FAtom's post-state into a per-theorem cache stored in
   plugin_data, so subsequent queries in the same theorem resume
   from the closest snapshot rather than re-walking. *)

structure TacticWalker :> sig
  (* Why a leaf didn't apply.  `CompileFailed' means its SML source
     didn't compile, which during a file's own compile means only
     that the file's `open's haven't run yet -- the names aren't
     there to be found.  Distinct from the tactic being run and
     refused by the goal. *)
  datatype failkind = ApplyFailed | CompileFailed

  (* Exposed because PolyML.compiler compiles at top level: these
     must be reachable by qualified name from the wrapped
     `TacticWalker.holder := SOME (…)` source that compileTactic
     runs.  Not part of the public API. *)
  val holder : Abbrev.tactic option ref
  val listHolder : Abbrev.list_tactic option ref

  val walkTo : {
    plugins: LSPExtension.plugin_data,
    theoremName: string,
    theoremStart: int,   (* file byte offset of the theorem's dec *)
    tacText: string,
    startState: goalFrag.goalstate,
    frags: TacticParse.tac_frag list,
    cursor: int
  } -> { state: goalFrag.goalstate,
         failedAt: (TacticParse.tac_frag * failkind) option }
end = struct

open TacticParse

val holder : Abbrev.tactic option ref = ref NONE
val listHolder : Abbrev.list_tactic option ref = ref NONE

(* Caches of compiled values, keyed by source text.  Per-atom
   PolyML.compiler invocation dominates walker cost — the point of
   `hol-lsp-goals-follow-cursor` is that auto-follow keystrokes should
   feel snappy.

   Their lifetime is one compile, not the process: a compiled tactic
   closes over the values its names had when it was compiled, and a
   recompile re-mints every constant the file defines (see `Context`'s
   note on `restore` — a later `new_definition` produces a fresh
   kernelid, and the old constant reads as retired).  A closure held
   across that boundary rewrites with theorems about constants the
   goal no longer mentions, so a tactic that closed its goal before
   the edit silently stops closing it after.  Cleared on compile
   start, below; within one compile they still serve every cursor
   movement, which is what auto-follow needs. *)
val compileCache: (string, Abbrev.tactic) Binarymap.dict ref =
  ref (Binarymap.mkDict String.compare)
val compileLTCache: (string, Abbrev.list_tactic) Binarymap.dict ref =
  ref (Binarymap.mkDict String.compare)

(* `holderName' is the ref the compiled source assigns into; `get' and
   `clear' read and reset that same ref at its own type. *)
fun compileVia {holderName, get, clear, cache} src =
  case Binarymap.peek (!cache, src) of
    SOME v => SOME v
  | NONE => let
      val wrapped = holderName ^ " := SOME (" ^ src ^ ");"
      val filtered = HOLSource.fromString
                       {quietOpen = true, print = fn _ => ()} wrapped
      val i = ref 0
      val n = String.size filtered
      fun read () = if !i >= n then NONE
                    else SOME (String.sub (filtered, !i)) before i := !i + 1
      fun swallow _ = ()
      val () = clear ()
      val _ = Portable.total (fn () => PolyML.compiler
                 (read, [PolyML.Compiler.CPErrorMessageProc swallow,
                         PolyML.Compiler.CPPrintStream swallow,
                         PolyML.Compiler.CPOutStream swallow,
                         PolyML.Compiler.CPNameSpace LSPNameSpace.fileNS]) ()) ()
      val () = case get () of
                 SOME v => cache := Binarymap.insert (!cache, src, v)
               | NONE => ()
      in get () end

fun compileTactic src = compileVia {
  holderName = "TacticWalker.holder",
  get = fn () => !holder, clear = fn () => holder := NONE,
  cache = compileCache} src

fun compileListTactic src = compileVia {
  holderName = "TacticWalker.listHolder",
  get = fn () => !listHolder, clear = fn () => listHolder := NONE,
  cache = compileLTCache} src

datatype failkind = ApplyFailed | CompileFailed
datatype applied = Applied of goalFrag.goalstate | Rejected of failkind

fun compileAndApply src state =
  case compileTactic src of
    NONE => Rejected CompileFailed
  | SOME tac =>
    (case Portable.total (goalFrag.expand tac (Context.snapshot())) state of
         NONE => Rejected ApplyFailed
       | SOME state' => Applied state')

(* `goalFrag.expand' runs a tactic once per focused goal, so a
   list_tactic smuggled in as `ALL_TAC >>> lt' only ever sees the
   singleton list made from one goal: REVERSE_LT that way is a no-op.
   `expand_list' hands it the whole focus, which is the point of it. *)
fun compileAndApplyLT src state =
  case compileListTactic src of
    NONE => Rejected CompileFailed
  | SOME lt =>
    (case Portable.total (goalFrag.expand_list lt (Context.snapshot()))
                         state of
         NONE => Rejected ApplyFailed
       | SOME state' => Applied state')

(* A branch whose tactics we skip.  `t >- tac' obliges tac to
   discharge the focused goal entirely, so its only effect on what
   follows is that one goal is gone -- which `cheat' reproduces
   exactly, at no cost.  Verified against real branches: the goal
   lists coincide. *)
fun cheatBranch state = compileAndApply "bossLib.cheat" state

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

   A list_tactic leaf is compiled and applied as one -- see
   `compileAndApplyLT'. *)
(* Source we made up, versus source the user wrote.  Only the
   second may fail to compile innocently -- that is the file's own
   compile reporting a typo, or its `open's not having run yet.  Ours
   failing to compile is a bug in this file and has to be seen. *)
datatype src = Synthesised of string | Verbatim of string

fun atomSrc tacText te = let
  val txt = textAt tacText
  (* `tr pat' spans the whole right operand of `>~', brackets and
     all -- as `Rename' also assumes -- so it is passed through, not
     wrapped again: wrapping produced `>~ [[pat]]', which never
     compiled.  And a selector is a list_tactic, wanted whole: run as
     `ALL_TAC >~ pats' through `expand' it saw each goal on its own
     and so could never pick one out.  Name the list_tactic itself
     and let `expand_list' hand it the focus. *)
  in case te of
      Subgoal span      => SOME (Synthesised
                                   ("BasicProvers.subgoal " ^ txt span))
    | LSelectGoal span  => SOME (Synthesised
                                   ("Q.SELECT_GOAL_LT " ^ txt span))
    | LSelectGoals span => SOME (Synthesised
                                   ("Q.SELECT_GOALS_LT " ^ txt span))
    | Rename span       => SOME (Synthesised ("Q.RENAME_TAC " ^ txt span))
    | _ => case topSpan te of
        SOME span => SOME (Verbatim (txt span))
      | NONE => Option.map Synthesised (printTacAsSML tacText te)
  end

(* Which leaves denote list_tactics.  Enumerated rather than read off
   `TacticParse.isTac', which also answers false for OOpaque -- a
   tactic sitting in a tactic list -- and so would misroute it. *)
fun isListTactic te = case te of
    LReverse => true
  | LSelectGoal _ => true
  | LSelectGoals _ => true
  | LFirst [] => true
  | LTacsToLT _ => true
  | LOpaque _ => true
  | _ => false

fun applyAtom tacText te state = case atomSrc tacText te of
    NONE => Applied state
  | SOME s => let
      val (src, ours) = case s of
          Synthesised x => (x, true)
        | Verbatim x => (x, false)
      val r = if isListTactic te then compileAndApplyLT src state
              else compileAndApply src state
      in case r of
           (* Our own source not compiling is not the user's problem
              to hide; report it like any other failure. *)
           Rejected CompileFailed => if ours then Rejected ApplyFailed else r
         | _ => r
      end

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

fun isThen1 FOpenThen1 = true
  | isThen1 _ = false

(* A missing start is not evidence of anything, so treat it as "the
   cursor is not before this". *)
fun startsAfter cursor start = case start of
    SOME s => cursor < s
  | NONE => false

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

(* Mirror of the above for start positions, used to keep the walker
   from running structure that lies after the cursor. *)
and fragStart frag = case frag of
    FAtom te => Option.map #1 (TacticSteps.atomSpan te)
  | FGroup ((s, _), _) => SOME s
  | FBracket (_, inner, _, te) =>
      bracketStartByte te (fn () => firstFragStart inner)
  | FMBracket (_, _, _, sections, te) =>
      bracketStartByte te (fn () => firstSectionStart sections)
  | FFOpen _ | FFMid _ | FFClose _ => NONE

and firstFragStart frags = case frags of
    [] => NONE
  | f :: rest =>
      (case fragStart f of NONE => firstFragStart rest | some => some)

and firstSectionStart sections = case sections of
    [] => NONE
  | sec :: rest =>
      (case firstFragStart sec of
         NONE => firstSectionStart rest
       | some => some)

and bracketStartByte te firstInner = case topSpan te of
    SOME (s, _) => SOME s
  | NONE => (case TacticSteps.atomSpan te of
      SOME (s, _) => SOME s
    | NONE => firstInner ())

(* `lastInner' is a thunk because it is only wanted for a wrapper
   whose own span is missing, as `LThen1's and `Try's are. *)
and bracketEndByte te lastInner = case topSpan te of
    SOME (_, e) => SOME e
  | NONE => (case atomEndByte te of
      SOME e => SOME e
    | NONE => lastInner ())

(* Steps a fragment list contributes to `stepIdx', mirroring exactly
   what the walk counts.  Skipping a branch must advance the index by
   what walking it would have, or snapshots recorded by one query
   won't line up with another's. *)
fun countSteps frags = case frags of
    [] => 0
  | FAtom (Subgoal _) :: FAtom LReverse :: rest => 1 + countSteps rest
  | f :: rest => countFrag f + countSteps rest

and countFrag f = case f of
    FAtom te => (case atomEndByte te of SOME _ => 1 | NONE => 0)
  | FGroup (_, inner) => countSteps inner
  | FBracket (_, inner, _, _) => countSteps inner
  | FMBracket (_, _, _, secs, _) =>
      List.foldl (fn (sec, n) => n + countSteps sec) 0 secs
  | FFOpen _ | FFMid _ | FFClose _ => 0

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
    compileCache := Binarymap.mkDict String.compare;
    compileLTCache := Binarymap.mkDict String.compare;
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
             at: tac_frag, why: failkind}

(* Constant across a walk.  `resumeIdx' is where a cached snapshot
   picks up: while `stepIdx' is below it the walk is replaying a
   prefix that snapshot already accounts for, so nothing in the
   prefix is applied again -- atoms are counted, opens, mids and
   closes passed over.  A bracket the resume point falls inside is
   thus entered without opening it and closed on the way back out,
   which is what a flat scan of the top-level fragments could not
   express: it gave up at the first nested fragment, so any `rpt' or
   `>-' before the cursor cost a full re-walk of the proof. *)
type walkenv = {tacText: string, cursor: int, resumeIdx: int,
                cheatLT: bool}

(* Set when a THENL branch was skipped.  Unlike `>-', a THENL branch
   need not discharge its goal, and closing the frame concatenates
   every branch's leftovers -- which `pp_goalstate' does, via `peek',
   whenever the focus ends up empty.  So the skip is optimistic: if
   the walk lands on an empty focus, `walkTo' runs it again with
   `cheatLT' false and reports that instead. *)
val cheatedLT = ref false

fun walkFrag (env as {tacText, cursor, resumeIdx, cheatLT}) state snaps
             stepIdx frag =
  let
    val replaying = stepIdx < resumeIdx
    fun keep idx = Done {state = state, snaps = snaps, stepIdx = idx}
  in case frag of
    FAtom te => (case atomEndByte te of
        SOME endB =>
          if replaying then keep (stepIdx + 1)
          else if cursor < endB then
            Halted {state = state, snaps = snaps, stepIdx = stepIdx}
          else (case applyAtom tacText te state of
                  Rejected why => Failed {state = state, snaps = snaps,
                                          stepIdx = stepIdx, at = frag,
                                          why = why}
                | Applied state' =>
                    Done {state = state',
                          snaps = {stepIdx = stepIdx, endByte = endB,
                                   state = state'} :: snaps,
                          stepIdx = stepIdx + 1})
      | NONE => (* no snap key: apply as an always-fires leaf (e.g. LReverse) *)
          if replaying then keep stepIdx
          else (case applyAtom tacText te state of
             Rejected why => Failed {state = state, snaps = snaps,
                                     stepIdx = stepIdx, at = frag, why = why}
           | Applied state' =>
               Done {state = state', snaps = snaps, stepIdx = stepIdx}))
  | FFOpen ok =>
      if replaying then keep stepIdx
      else (case applyOpen ok state of
         NONE => Failed {state = state, snaps = snaps,
                         stepIdx = stepIdx, at = frag, why = ApplyFailed}
       | SOME state' =>
           Done {state = state', snaps = snaps, stepIdx = stepIdx})
  | FFMid m =>
      if replaying then keep stepIdx
      else (case applyMid m state of
         NONE => Failed {state = state, snaps = snaps,
                         stepIdx = stepIdx, at = frag, why = ApplyFailed}
       | SOME state' =>
           Done {state = state', snaps = snaps, stepIdx = stepIdx})
  | FFClose c =>
      if replaying then keep stepIdx
      else (case applyClose c state of
         NONE => Failed {state = state, snaps = snaps,
                         stepIdx = stepIdx, at = frag, why = ApplyFailed}
       | SOME state' =>
           Done {state = state', snaps = snaps, stepIdx = stepIdx})
  | FGroup (_, inner) => walkFrags env state snaps stepIdx inner
  (* Transparent bracket: `open_null_ok`'s Parallel frame would
     hide the inner TacsToLT context from `pp_goalstate`. *)
  | FBracket (FOpenNullOk, inner, _, _) =>
      walkFrags env state snaps stepIdx inner
  | FBracket (ok, inner, cc, te) =>
      (case bracketEndByte te (fn () => lastFragEnd inner) of
        SOME be =>
          (* Cursor before the combinator: it hasn't run yet, so show
             the goals it is about to act on rather than opening it. *)
          if not replaying andalso
             startsAfter cursor (bracketStartByte te
                                   (fn () => firstFragStart inner)) then
            Halted {state = state, snaps = snaps, stepIdx = stepIdx}
          else let
            fun opened k =
              if replaying then k state
              else (case applyOpen ok state of
                      NONE => Failed {state = state, snaps = snaps,
                                      stepIdx = stepIdx, at = FFOpen ok,
                                       why = ApplyFailed}
                    | SOME state' => k state')
            (* A bracket wholly inside the replayed prefix had its
               close accounted for as well as its open. *)
            fun closed r =
              if #stepIdx r < resumeIdx then Done r
              else (case applyClose cc (#state r) of
                      NONE => Failed {state = #state r, snaps = #snaps r,
                                      stepIdx = #stepIdx r, at = FFClose cc,
                                       why = ApplyFailed}
                    | SOME state'' =>
                        Done {state = state'', snaps = #snaps r,
                              stepIdx = #stepIdx r})
          in
            if cursor < be then
              (* Open, walk inner as far as cursor lets us; don't close. *)
              opened (fn state' =>
                case walkFrags env state' snaps stepIdx inner of
                  Done r => Halted {state = #state r, snaps = #snaps r,
                                    stepIdx = #stepIdx r}
                | out => out)
            else if isThen1 ok andalso not replaying then
              (* Cursor past a finished `>-' branch: it had to prove
                 the focused goal, so skip its tactics and take the
                 one thing that outlives it. *)
              opened (fn state' =>
                case cheatBranch state' of
                  Rejected why => Failed {state = state', snaps = snaps,
                                          stepIdx = stepIdx, at = frag,
                                          why = why}
                | Applied state'' =>
                    closed {state = state'', snaps = snaps,
                            stepIdx = stepIdx + countSteps inner})
            else
              (* Cursor past the whole bracket: open + walk + close. *)
              opened (fn state' =>
                case walkFrags env state' snaps stepIdx inner of
                  Done r => closed r
                | out => out)
          end
      | NONE => (* no end position: bail as opaque *)
          Failed {state = state, snaps = snaps,
                  stepIdx = stepIdx, at = frag, why = ApplyFailed})
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
            fun walkSections mayCheat state snaps stepIdx sections =
              case sections of
                [] => Done {state = state, snaps = snaps, stepIdx = stepIdx}
              | [sec] => walkFrags env state snaps stepIdx sec
              | sec :: rest =>
                  if mayCheat andalso cheatLT andalso stepIdx >= resumeIdx
                     andalso cursor >= Option.getOpt
                                         (firstSectionStart rest, be)
                  then
                    (* This branch's turn is over and the cursor is
                       still inside the block, so only its effect on
                       the branches after it matters -- and that is
                       nothing: each gets its own goal, fixed when the
                       block opened. *)
                    (cheatedLT := true;
                     case cheatBranch state of
                       Rejected why => Failed {state = state, snaps = snaps,
                                               stepIdx = stepIdx,
                                               at = FFMid mid, why = why}
                     | Applied state' =>
                       (case applyMid mid state' of
                          NONE => Failed {state = state', snaps = snaps,
                                          stepIdx = stepIdx, at = FFMid mid,
                                           why = ApplyFailed}
                        | SOME state'' =>
                            walkSections mayCheat state'' snaps
                              (stepIdx + countSteps sec) rest))
                  else
                  (case walkFrags env state snaps stepIdx sec of
                     Done r =>
                       if #stepIdx r < resumeIdx then
                         (* still replaying: this mid already fired *)
                         walkSections mayCheat (#state r) (#snaps r)
                                      (#stepIdx r) rest
                       (* `walkFrags' says Done as soon as a section's
                          frags run out, which for an ALL_TAC branch is
                          immediately.  Only advance once the cursor has
                          actually reached the next section, so the text
                          between two branches reports the first one's
                          result -- solved, or its leftover goals. *)
                       else if cursor <
                               Option.getOpt (firstSectionStart rest, be)
                       then Halted {state = #state r, snaps = #snaps r,
                                    stepIdx = #stepIdx r}
                       else
                       (case applyMid mid (#state r) of
                          NONE => Failed {state = #state r,
                                          snaps = #snaps r,
                                          stepIdx = #stepIdx r,
                                          at = FFMid mid,
                                          why = ApplyFailed}
                        | SOME state' =>
                            walkSections mayCheat state' (#snaps r)
                                         (#stepIdx r) rest)
                   | out => out)
            fun opened k =
              if replaying then k state
              else (case applyOpen ok state of
                      NONE => Failed {state = state, snaps = snaps,
                                      stepIdx = stepIdx, at = FFOpen ok,
                                       why = ApplyFailed}
                    | SOME state' => k state')
            fun closed r =
              if #stepIdx r < resumeIdx then Done r
              else (case applyClose cc (#state r) of
                      NONE => Failed {state = #state r, snaps = #snaps r,
                                      stepIdx = #stepIdx r, at = FFClose cc,
                                       why = ApplyFailed}
                    | SOME state'' =>
                        Done {state = state'', snaps = #snaps r,
                              stepIdx = #stepIdx r})
          in
            if not replaying andalso
               startsAfter cursor
                 (bracketStartByte te
                    (fn () => firstSectionStart sections))
            then
              Halted {state = state, snaps = snaps, stepIdx = stepIdx}
            else if cursor < be then
              opened (fn state' =>
                case walkSections true state' snaps stepIdx sections of
                  Done r => Halted {state = #state r, snaps = #snaps r,
                                    stepIdx = #stepIdx r}
                | out => out)
            else
              (* Past the `]': the closed state concatenates every
                 branch's leftovers, so they all have to be real. *)
              opened (fn state' =>
                case walkSections false state' snaps stepIdx sections of
                  Done r => closed r
                | out => out)
          end
      | NONE => Failed {state = state, snaps = snaps,
                        stepIdx = stepIdx, at = frag, why = ApplyFailed})
  end

and walkFrags (env as {tacText, cursor, resumeIdx, ...}) state snaps
              stepIdx frags =
  case frags of
    [] => Done {state = state, snaps = snaps, stepIdx = stepIdx}
  (* `sg q' immediately followed by REVERSE_LT is how TacticParse
     encodes `suffices_by' -- it is the very shape `optTree' folds
     back into the surface operator when printing.  Applying the two
     separately is not the same tactic: it leaves `w' with `q' stripped
     into the assumptions, whereas HOL's suffices_by is
     `Q_TAC SUFF_TAC', whose first subgoal is the implication
     `q ==> w'.  Tactics that begin by discharging that implication --
     strip_tac, and often rw -- fail against the assumption form.  So
     apply the pair as the single primitive it stands for. *)
  | FAtom (te as Subgoal span) :: FAtom LReverse :: rest =>
      (case atomEndByte te of
         SOME endB =>
           if stepIdx < resumeIdx then
             walkFrags env state snaps (stepIdx + 1) rest
           else if cursor < endB then
             Halted {state = state, snaps = snaps, stepIdx = stepIdx}
           else (case compileAndApply
                        ("Tactical.Q_TAC Tactic.SUFF_TAC "
                         ^ textAt tacText span) state of
                   Rejected why => Failed {state = state, snaps = snaps,
                                           stepIdx = stepIdx, at = FAtom te,
                                           why = why}
                 | Applied state' =>
                     walkFrags env state'
                       ({stepIdx = stepIdx, endByte = endB,
                         state = state'} :: snaps)
                       (stepIdx + 1) rest)
       | NONE => Failed {state = state, snaps = snaps,
                         stepIdx = stepIdx, at = FAtom te, why = ApplyFailed})
  | f :: rest =>
      (case walkFrag env state snaps stepIdx f of
         Done r =>
           walkFrags env (#state r) (#snaps r) (#stepIdx r) rest
       | out => out)

fun walkTo {plugins, theoremName, theoremStart, tacText, startState,
            frags, cursor} = let
  val cacheRefOpt = LSPExtension.getPluginData (plugins, cacheTag)
  val (resumeIdx, resumeState, priorSnaps) =
    resumeFrom cacheRefOpt
      {theoremName = theoremName, tacText = tacText, cursor = cursor}
      startState
  fun run cheatLT idx state =
    (cheatedLT := false;
     walkFrags {tacText = tacText, cursor = cursor, resumeIdx = idx,
                cheatLT = cheatLT}
               state priorSnaps 0 frags
     handle Portable.Interrupt =>
       Halted {state = state, snaps = priorSnaps, stepIdx = idx})
  val outcome = run true resumeIdx resumeState
  (* Finishing the fragments while still replaying means the cached
     index doesn't match them any more -- fewer atoms than the
     snapshot counted.  Start over rather than report a state that
     nothing was applied to. *)
  val outcome = case outcome of
      Done r => if resumeIdx > 0 andalso #stepIdx r < resumeIdx
                then run true 0 startState else outcome
    | _ => outcome
  fun stateOf out = case out of
      Done r => #state r | Halted r => #state r | Failed r => #state r
  (* An empty focus is where `pp_goalstate' closes the enclosing
     frame to show what remains, and a closed THENL wants every
     branch's real leftovers.  Redo without skipping any. *)
  val outcome =
    if !cheatedLT andalso null (goalFrag.top_goals (stateOf outcome))
    then run false resumeIdx resumeState
    else outcome
  val (finalState, allSnaps, failedAt) = case outcome of
      Done r    => (#state r, #snaps r, NONE)
    | Halted r  => (#state r, #snaps r, NONE)
    | Failed r  => (#state r, #snaps r, SOME (#at r, #why r))
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
