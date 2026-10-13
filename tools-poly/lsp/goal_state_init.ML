(* LSPExtension.goalStateAtPos: given the enclosing Theorem's
   statement quote and tactic body, walk the tactic stepwise via
   goalFrag and return the goal-state at the cursor. *)

(* The goal a `Resume thm[label]:' body discharges -- whatever the
   parent proof suspended under `label'.

   A ref filled in from `tools-poly/hol.ML' rather than a direct
   `markerLib' call, because this file is `QUse'd at LSP startup
   against whatever heap the buffer's directory asks for, and
   everything up to `src/boss' asks for `hol.state0', which has no
   `markerLib'.  Naming it here would take the whole goal-state hook
   down in those directories, silently.

   NONE means "no such suspension", which is the ordinary state until
   the parent's proof has been run for real. *)
structure LSPSuspendedGoal = struct
  val lookup: ({suspension: string, label: string} ->
               (Term.term list * Term.term) option) ref = ref (fn _ => NONE)
end

(* The goal a `Definition foo: <eqns> Termination tac End' body
   discharges -- the termination obligation the definition principle
   derives from `<eqns>'.

   Filled in from `tools-poly/hol.ML' for the same reason as the
   suspension lookup above: building it needs `Defn', which `hol.state0'
   does not have, and naming it here would take the whole goal-state
   hook down in every directory up to `src/boss'.  Unlike that one this
   file may still name `Term.term' -- it is loaded against a heap, and
   the kernel is in every heap; only `LSPExtension' is below it.

   Three answers rather than an option, because the two reasons for
   having no goal call for different things to be said: a definition
   that needs no termination proof is fine and its tactic is dead, and
   a definition that will not build has nothing to say yet. *)
structure LSPTerminationGoal = struct
  datatype result =
      Obligation of Term.term list * Term.term
    | NoObligation of string
    | Unavailable of string
  val lookup: ({stem: string, quote: string} -> result) ref =
      ref (fn _ => Unavailable
             "termination goals need `Defn', which this directory's heap \
             \does not have")
end

local
  open TacticParse

  val walkerBudgetMs = 1500

  (* The backstop on the whole answer, as against `walkerBudgetMs` on
     the walk alone.  Deliberately loose: it is not there to keep the
     goals pane responsive -- that is the walk's budget, and it is two
     orders of magnitude tighter -- but to stop one request owning the
     process's compile state for ever.  Everything else that wants to
     rewind the Context, a compile included, waits behind this one.

     So it should fire only where nothing else can help, and never
     where the work was merely slow: a first request against a cold
     walker cache, which has to compile the tactic's leaves, is
     seconds. *)
  val hookBudgetMs = 30000

  fun logStderr s =
    (TextIO.output (TextIO.stdErr, s); TextIO.flushOut TextIO.stdErr)

  fun withTimeout ms f = let
    val here = Thread.self ()
    val done = ref false
    val timedOut = ref false
    val mtx = Mutex.mutex ()
    fun markDone () =
      (Mutex.lock mtx; done := true; Mutex.unlock mtx)
    fun canary () = (
      OS.Process.sleep (Time.fromMilliseconds ms);
      Mutex.lock mtx;
      (if !done then ()
       else (logStderr ("goal-state walker exceeded " ^
                        LargeInt.toString ms ^ "ms budget; interrupting\n");
             timedOut := true;
             Thread.interrupt here));
      Mutex.unlock mtx)
    val _ = Thread.fork (canary, [])
    (* Captured, not allowed to propagate.  The canary's interrupt
       arrives as an exception inside `f', and whether anything catches
       it on the way out is not ours to decide: a tactic walk swallows
       it and reports the leaf as failed, while a pretty-printer or a
       parser lets it straight through.  Releasing it unchanged would
       make the budget's effect depend on which of those the walk
       happened to be in -- an empty goal state from one, a raise out of
       the hook from the other.  So: if the canary fired, the budget is
       the answer and whatever `f' raised on its way out is that
       interrupt arriving; otherwise the exception is the caller's and
       goes back to them intact. *)
    val r = Exn.capture (fn () =>
              Thread_Attributes.with_attributes
                Thread_Attributes.private_interrupts (fn _ => f ())) ()
    val () = markDone ()
  in if !timedOut then NONE else SOME (Exn.release r) end

  (* Rendered at the width the client says its pane is, so the line
     breaking the pretty printer chooses is the one the reader sees.
     `Globals.linewidth' is what `term_to_string' consults, so the
     structured per-goal strings need it set around them too. *)
  fun ppGoal width (asms, g) = let
    fun str t = Lib.with_flag (Globals.linewidth, width)
                              Parse.term_to_string t
    in {asms = List.map str asms, goal = str g} end
  (* `pp_goals_only', not `pp_goalstate': the combinator tags and the
     note about a solved focus go in `context' and `note', so a client
     can keep them where the goals scrolling does not take them with
     it.  Rendering them here too would show them twice. *)
  fun ppState width st =
    Lib.with_flag (Parse.current_backend, PPBackEnd.vt100_terminal)
      (HOLPP.pp_to_string width goalFrag.pp_goals_only) st
    handle _ => ""

  (* The same state, rendered again through the back end that says in
     data what `vt100_terminal` says in colour, then taken apart.  Two
     passes rather than one because `pretty` is what most clients
     render and it should not change: a client that wants the
     annotations rebuilds the text from these instead.

     The two agree on where the lines break.  `lsp_terminal` emits its
     delimiters with `add_stringsz (_, 0)` and delegates every layout
     operation to `raw_terminal`, so the annotations are invisible to
     the pretty-printer's width arithmetic -- which the selftest holds
     it to, since a disagreement would silently hand clients segments
     that do not match the text beside them. *)
  fun ppSegments width st =
    PPBackEnd.lsp_segments
      (Lib.with_flag (Parse.current_backend, PPBackEnd.lsp_terminal)
         (HOLPP.pp_to_string width goalFrag.pp_goals_only) st)
    handle _ => []

  val fragEndByte = TacticSteps.atomEndByte

  fun stepIndex (frags, cursor) = let
    fun go [] n = n
      | go (FAtom te :: rest) n = (case fragEndByte te of
          SOME e => if cursor < e then n else go rest (n + 1)
        | NONE => go rest n)
      | go (FGroup (_, inner) :: rest) n = go rest (go inner n)
      | go (FBracket (_, inner, _, _) :: rest) n = go rest (go inner n)
      | go (FMBracket (_, _, _, sections, _) :: rest) n =
          go rest (List.foldl (fn (s, m) => go s m) n sections)
      | go (_ :: rest) n = go rest n
    in go frags 0 end

  (* User-facing error message per failing frag.  Uses the surface
     sugar name rather than the internal synthesis (e.g. "Selector
     `>~ [pat]` found no matching subgoal", not the `ALL_TAC >~ …`
     wrapper the walker actually compiled). *)
  fun failMsg tacText frag = case frag of
      FAtom (Subgoal span) =>
        "Subgoal `" ^ String.substring
                        (tacText, #1 span, #2 span - #1 span)
        ^ "` by … failed to prove"
      (* The span covers the bracketed list already. *)
    | FAtom (LSelectGoal span) =>
        "Selector `>~ "
        ^ String.substring (tacText, #1 span, #2 span - #1 span)
        ^ "` found no matching subgoal"
    | FAtom (LSelectGoals span) =>
        "Selector `>>~ "
        ^ String.substring (tacText, #1 span, #2 span - #1 span)
        ^ "` found no matching subgoal"
    | FAtom LReverse =>
        "`suffices_by` reversal failed"
    | FAtom te => (case topSpan te of
        SOME (s, e) =>
          "Tactic `" ^ String.substring (tacText, s, e - s)
          ^ "` failed to apply"
        (* No whole-expression span (MapEvery, Rename, ...); recover
           the surface call from TacticParse's inverse printer. *)
      | NONE => (case printTacAsSML tacText te of
            SOME src => "Tactic `" ^ src ^ "` failed to apply"
          | NONE => "This step failed to apply"))
      (* These four are the walk reporting on itself: it could not get
         into, through, or out of a piece of structure.  They used to
         name the walker's own vocabulary -- "Combinator open failed"
         -- at a reader with no way to know what a combinator open is,
         and no action to take if they did.  What a reader can act on
         is which goals the step had to work with, so say that. *)
    | FFOpen _  => "No goal here for this step to act on"
    | FFMid _   => "No goal left for the next branch of this step"
    | FFClose _ => "This step did not finish with the goals it was given"
    | FGroup _  => "The tactics in this group left the goal unfinished"
      (* A bracket reported as a whole is one whose close would not go
         through.  Three of them say something: each obliged what it
         brackets to prove a goal, and it did not. *)
    | FBracket (FOpenThen1 _, _, _, _) =>
        "`>-` branch did not prove its goal"
    | FBracket (FOpenBy _, _, _, _) =>
        "`by` assertion was not proved by its tactic"
    | FBracket (FOpenSufficesBy _, _, _, _) =>
        "`suffices_by` reduction was not proved by its tactic"
    | FBracket _  => "The tactics in these brackets left the goal \
                     \unfinished"
    | FMBracket _ => "The tactics in these brackets left the goal \
                     \unfinished"

  (* A leaf whose SML source didn't compile says nothing about the
     proof.  Either the file's compile hasn't run the `open's yet, in
     which case the answer is provisional; or it has, and the compile
     already published the real message against that very text -- so
     repeating it as "failed to apply" would both duplicate it and
     misdescribe it. *)
  fun sourceFailure (_, TacticWalker.CompileFailed) = true
    | sourceFailure _ = false

  (* Does this failure say something about the *proof*, or about the
     walk?

     `failMsg' above has two kinds of answer.  One names a tactic that
     would not apply, or a branch that was obliged to prove its goal
     and did not: a reader can go and look at that.  The other --
     "Combinator open failed", "Group failed", "Bracket failed" -- says
     the walk could not get through a piece of structure, which is a
     statement about the walker's own progress from wherever the cursor
     put it.  Parking the cursor just past a `>-' is enough to produce
     one.

     Only the first kind earns a range, and so a squiggle.  The second
     still travels as `error', because a goals pane asking about that
     exact spot has nothing else to show, but it is not recorded
     against the file: the server accumulates located failures until
     the next compile, and a mark that depends on where the cursor was
     would sit there afterwards claiming to be a property of the
     text. *)
  fun aboutTheProof frag =
    case frag of
        FAtom _                            => true
      | FBracket (FOpenThen1 _, _, _, _)   => true
      | FBracket (FOpenBy _, _, _, _)      => true
      | FBracket (FOpenSufficesBy _, _, _, _) => true
      | _ => false

  (* Where in the file to point at what failed, as a pair: the range
     the message belongs on, and a second one closing it off.

     `fragSpan' answers for a bracket as well as a leaf, falling back
     to the contents when the combinator has no span of its own.  For
     the three combinators that oblige what they bracket to prove a
     goal, that fallback is the whole branch -- and a branch that
     proves nothing yet is usually the very thing being written, so
     marking all of it tells the reader what they already know and
     buries the message in it.  Point at the combinator that made the
     demand instead, and separately at the paren closing what it was
     demanded of.

     For `by' and `suffices_by' the demand is the assertion as much as
     the keyword, and the two together are short, so the first range
     runs from the assertion through the keyword. *)
  fun failRanges tacText tacStart frag = let
    fun shift (s, e) = (tacStart + s, tacStart + e)
    val whole = TacticWalker.fragSpan frag
    fun openOf (FBracket (ok, _, _, _)) = SOME ok
      | openOf (FFOpen ok) = SOME ok
      | openOf _ = NONE
    (* The branch's own `)', when it has one.  Taken from the body
       group's span rather than by looking for a `)' at the end of the
       branch: in `>- metis_tac (foo x)' the last character is a paren
       too, and it is the argument's.  An unclosed branch parses to a
       RepairGroup whose span ends at the next token, so the character
       test rejects it. *)
    val close = case frag of
        FBracket (_, [FGroup ((s, e), _)], _, _) =>
          if s >= 0 andalso e <= size tacText andalso e - s >= 2
             andalso String.sub (tacText, s) = #"("
             andalso String.sub (tacText, e - 1) = #")"
          then SOME (e - 1, e) else NONE
      | _ => NONE
    val first = case (openOf frag, TacticWalker.combinatorSpan frag) of
        (SOME (FOpenThen1 _), SOME k) => SOME k
      | (SOME _, SOME (ks, ke)) =>
          (case whole of
               SOME (s, _) => SOME (Int.min (s, ks), ke)
             | NONE => SOME (ks, ke))
      | _ => whole
  in (Option.map shift first, Option.map shift close) end
in

val () = LSPExtension.goalStateAtPos :=
  (fn ({plugins, width, ...}: LSPExtension.hover_context,
       {name, quote, quoteStart, tacText, tacStart, cursor, compileDone,
        resumeOf, terminationOf, locate}
         : LSPExtension.theorem_context) => let
    (* The budget covers the whole answer, not just the walk.

       Its caller holds the process's compile state for as long as this
       runs -- it has rewound the Context to this theorem's snapshot and
       must put it back before anything else may rewind it -- so every
       part of this that can run long is part of what a compile and the
       next goal-state request are waiting on.  The walk is the part
       most likely to, but it is not the only one: parsing the statement
       and rendering the goals both run user-supplied code (a custom
       parser, a pretty-printer) that can loop.  Bounding only the walk
       left those able to wedge the process.

       `step` is 0 on this path because nothing got far enough to count
       one.  The server reads a response carrying `error` without a
       `failedRange` as "this walk learned nothing", so a 0 here cannot
       be mistaken for a walk that reached the start and stopped. *)
    fun timedOutResponse () =
      SOME {theorem = name, step = 0,
            goals = [], pretty = "", context = [],
            note = NONE, status = "ok",
            error = SOME ("goal state timed out (>"
                          ^ LargeInt.toString hookBudgetMs ^ "ms)"),
            failedRange = NONE, failedCloseRange = NONE,
            segments = []}
    fun answer () = let
    (* A Termination block's obligation, when that is what the cursor
       is in.  No budget of its own: `Hol_defn' on a body halfway
       through being typed can run a long way, and so can parsing a
       statement, which is why the budget above covers the whole
       answer rather than the walk alone. *)
    val tcResult =
      case terminationOf of
          NONE => NONE
        | SOME {stem} =>
          SOME (!LSPTerminationGoal.lookup {stem = stem, quote = quote})
    (* A Theorem carries its goal in the file and it is parsed; a
       Resume's is in the suspension store and it is looked up; a
       Termination's is derived from the equations beside it.  All
       three answer with a whole goal, assumptions included: the
       suspended one routinely has them, `resumption_to_goal' having
       folded the `suspendimp' chain back into an assumption list. *)
    val startGoal: (Term.term list * Term.term) option =
      case (terminationOf, resumeOf) of
          (SOME _, _) =>
          (case tcResult of
               SOME (LSPTerminationGoal.Obligation g) => SOME g
             | _ => NONE)
        | (NONE, SOME r) => !LSPSuspendedGoal.lookup r
        | (NONE, NONE) => Option.map (fn tm => ([], tm))
                                     (Lib.total Parse.Term [QUOTE quote])
    (* What the walker's cache addresses an entry by, beside the
       tactic text.  A Resume's `quote' is empty, so the parse is no
       use as a validator; the goal it opens on is the thing that
       would have to change.  A Termination's `quote' is the equations,
       which is exactly what would have to change for the obligation to
       be a different one. *)
    val goalText =
      case (resumeOf, startGoal) of
          (NONE, _) => quote
        | (SOME _, NONE) => quote
        | (SOME _, SOME (asl, g)) =>
          String.concatWith "\n"
            (List.map Parse.term_to_string asl @ [Parse.term_to_string g])
    val frags = TacticSteps.fragsOfTacText
                  {label = "goal_state", tacText = tacText}
    val tacCursor = cursor - tacStart
    in case (startGoal, frags) of
         (SOME goal, SOME fs) => let
           val startState = goalFrag.new_goal goal
           val step = stepIndex (fs, tacCursor)
           in case withTimeout walkerBudgetMs (fn () =>
                    TacticWalker.walkTo {
                      plugins = plugins, theoremName = name,
                      theoremStart = quoteStart, goalText = goalText,
                      tacText = tacText, startState = startState,
                      frags = fs, cursor = tacCursor,
                      stopAtFail = locate}) of
                NONE => SOME
                  {theorem = name, step = step,
                   goals = [], pretty = "", context = [],
                   note = NONE, status = "ok",
                   error = SOME ("walker timed out (>"
                                 ^ LargeInt.toString walkerBudgetMs ^ "ms)"),
                   failedRange = NONE, failedCloseRange = NONE,
                   segments = []}
              | SOME {state, failedAt, recovered} => let
                  (* Where the walk came to rest is the news, unless
                     coming to rest is all it describes.  A walk that
                     recovered from a real failure and then could not
                     get through some piece of structure reports the
                     structure, which says nothing about the proof and
                     buries the thing that does: on cakeml's
                     `lex_aux_sexp_to_list' that replaced the failing
                     `drule_all' with a combinator the reader has no
                     quarrel with. *)
                  val failedAt = case failedAt of
                      SOME (frag, _) =>
                        if aboutTheProof frag then failedAt
                        else (case recovered of
                                  SOME f => SOME f
                                | NONE => failedAt)
                    | NONE => NONE
                  val silent = case failedAt of
                      SOME f => sourceFailure f
                    | NONE => false
                  val reported = if silent then NONE else failedAt
                  val ranges = case reported of
                      NONE => (NONE, NONE)
                    | SOME (frag, _) =>
                      if aboutTheProof frag
                      then failRanges tacText tacStart frag
                      else (NONE, NONE)
                  (* Every goal discharged -- but by `cheat', standing
                     in for the branch that failed, so the walk is past
                     the point where anything it says is established.
                     `pp_goals_only' renders an empty focus as "Initial
                     goal proved.", which for a proof that demonstrably
                     does not go through is simply false, and it is the
                     first thing a reader sees. *)
                  val onlyCheats =
                    isSome reported andalso
                    null (goalFrag.top_goals state)
                  in SOME
                  {theorem = name, step = step,
                   goals = List.map (ppGoal width) (goalFrag.top_goals state),
                   pretty = if onlyCheats
                            then "No goals remain, but only because `cheat' \
                                 \stood in for the branch that failed: \
                                 \the proof does not close."
                            else ppState width state,
                   context = goalFrag.context_lines state,
                   note = goalFrag.focus_note state,
                   status = if silent andalso not compileDone
                            then "pending" else "ok",
                   error = Option.map (failMsg tacText o #1) reported,
                   failedRange = #1 ranges,
                   failedCloseRange = #2 ranges,
                   segments = if onlyCheats then []
                              else ppSegments width state}
                  end
           end
       | (SOME goal, NONE) => let
           val startState = goalFrag.new_goal goal
           in SOME {theorem = name, step = 0,
                    goals = [ppGoal width goal],
                    pretty = ppState width startState,
                    context = goalFrag.context_lines startState,
                    note = goalFrag.focus_note startState,
                    status = "ok", error = NONE,
                    failedRange = NONE, failedCloseRange = NONE,
                    segments = ppSegments width startState}
           end
       (* A statement that does not parse says nothing, and `null' is
          the honest answer.  A Resume is different: the block is
          there and the cursor is in it, so `null' would read as "no
          goal state here" -- a fault in the proof.  The subgoal is
          simply not available yet, which is what `pending' says.  No
          `failedRange' with it, so nothing is squiggled: the server
          only makes a diagnostic when a range and a message arrive
          together.

          A Termination block is the Resume case again, with one extra
          answer: a definition that needs no termination proof is not
          waiting for anything, and its tactic is simply dead code.
          That goes in `note', the line above the goals, rather than in
          `error', which this signature reserves for a walk that gave
          up or a tactic that failed. *)
       | (NONE, _) => let
           fun blank {status, note, error} =
             SOME {theorem = name, step = 0, goals = [], pretty = "",
                   context = [], note = note, status = status,
                   error = error, failedRange = NONE,
                   failedCloseRange = NONE, segments = []}
         in case (tcResult, resumeOf) of
                (SOME (LSPTerminationGoal.NoObligation m), _) =>
                blank {status = "ok", note = SOME m, error = NONE}
              | (SOME (LSPTerminationGoal.Unavailable m), _) =>
                blank {status = "pending", note = NONE, error = SOME m}
                (* `Obligation' cannot reach here: it is what makes
                   `startGoal' a `SOME'. *)
              | (SOME (LSPTerminationGoal.Obligation _), _) => NONE
              | (NONE, NONE) => NONE
              | (NONE, SOME {suspension, label}) =>
                blank {status = "pending", note = NONE,
                       error = SOME ("no subgoal suspended under `" ^ label ^
                                     "' by " ^ suspension ^ " (yet): its \
                                     \proof has to run before the subgoal \
                                     \exists")}
         end
    end
    in case withTimeout hookBudgetMs answer of
           NONE => timedOutResponse ()
         | SOME r => r
    end)

end;
