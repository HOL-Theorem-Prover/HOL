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

local
  open TacticParse

  val walkerBudgetMs = 1500

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
    val r = Thread_Attributes.with_attributes
              Thread_Attributes.private_interrupts (fn _ => f ())
    val () = markDone ()
  in if !timedOut then NONE else SOME r end

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
          | NONE => "Structural leaf failed"))
    | FFOpen _  => "Combinator open failed"
    | FFMid _   => "Combinator branch-advance failed"
    | FFClose _ => "Combinator close failed"
    | FGroup _  => "Group failed"
      (* A bracket reported as a whole is one whose close would not go
         through.  Three of them say something: each obliged what it
         brackets to prove a goal, and it did not. *)
    | FBracket (FOpenThen1 _, _, _, _) =>
        "`>-` branch did not prove its goal"
    | FBracket (FOpenBy _, _, _, _) =>
        "`by` assertion was not proved by its tactic"
    | FBracket (FOpenSufficesBy _, _, _, _) =>
        "`suffices_by` reduction was not proved by its tactic"
    | FBracket _  => "Bracket failed"
    | FMBracket _ => "Bracket failed"

  (* A leaf whose SML source didn't compile says nothing about the
     proof.  Either the file's compile hasn't run the `open's yet, in
     which case the answer is provisional; or it has, and the compile
     already published the real message against that very text -- so
     repeating it as "failed to apply" would both duplicate it and
     misdescribe it. *)
  fun sourceFailure (_, TacticWalker.CompileFailed) = true
    | sourceFailure _ = false

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
        resumeOf}
         : LSPExtension.theorem_context) => let
    (* A Theorem carries its goal in the file and it is parsed; a
       Resume's is in the suspension store and it is looked up.  Both
       answer with a whole goal, assumptions included: the suspended
       one routinely has them, `resumption_to_goal' having folded the
       `suspendimp' chain back into an assumption list. *)
    val startGoal: (Term.term list * Term.term) option =
      case resumeOf of
          NONE => Option.map (fn tm => ([], tm))
                             (Lib.total Parse.Term [QUOTE quote])
        | SOME r => !LSPSuspendedGoal.lookup r
    (* What the walker's cache addresses an entry by, beside the
       tactic text.  A Resume's `quote' is empty, so the parse is no
       use as a validator; the goal it opens on is the thing that
       would have to change. *)
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
                      frags = fs, cursor = tacCursor}) of
                NONE => SOME
                  {theorem = name, step = step,
                   goals = [], pretty = "", context = [],
                   note = NONE, status = "ok",
                   error = SOME ("walker timed out (>"
                                 ^ LargeInt.toString walkerBudgetMs ^ "ms)"),
                   failedRange = NONE, failedCloseRange = NONE,
                   segments = []}
              | SOME {state, failedAt} => let
                  val silent = case failedAt of
                      SOME f => sourceFailure f
                    | NONE => false
                  val reported = if silent then NONE else failedAt
                  val ranges = case reported of
                      NONE => (NONE, NONE)
                    | SOME (frag, _) => failRanges tacText tacStart frag
                  in SOME
                  {theorem = name, step = step,
                   goals = List.map (ppGoal width) (goalFrag.top_goals state),
                   pretty = ppState width state,
                   context = goalFrag.context_lines state,
                   note = goalFrag.focus_note state,
                   status = if silent andalso not compileDone
                            then "pending" else "ok",
                   error = Option.map (failMsg tacText o #1) reported,
                   failedRange = #1 ranges,
                   failedCloseRange = #2 ranges,
                   segments = ppSegments width state}
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
          together. *)
       | (NONE, _) =>
         (case resumeOf of
              NONE => NONE
            | SOME {suspension, label} => SOME
                {theorem = name, step = 0, goals = [], pretty = "",
                 context = [], note = NONE, status = "pending",
                 error = SOME ("no subgoal suspended under `" ^ label ^
                               "' by " ^ suspension ^ " (yet): its proof \
                               \has to run before the subgoal exists"),
                 failedRange = NONE, failedCloseRange = NONE,
                 segments = []})
    end)

end;
