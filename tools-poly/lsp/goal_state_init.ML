(* LSPExtension.goalStateAtPos: given the enclosing Theorem's
   statement quote and tactic body, walk the tactic stepwise via
   goalFrag and return the goal-state at the cursor. *)

local
  (* Wall-clock budget on the walker.  Users routinely park their
     cursor past the last tactic in a Proof block; that tactic is
     often a closer (METIS_TAC, DECIDE_TAC, …) that takes seconds
     to run.  Without a budget the walker executes it every time
     the auto-follow request fires, and the LSP hangs.  The canary
     Thread.interrupts this thread when the budget expires; the
     walker's `Portable.Interrupt` handler catches, flushes its
     snapshot cache, and returns the pre-step state.

     `src/portableML/poly/concurrent/Timeout.sml` implements this
     shape properly (with Event_Timer + race-safe cancel), but it
     isn't linked into the LSP heap; the hand-rolled canary below
     avoids the extra dependency.

     Long enough that most closers complete, short enough that stalls
     stay off the interactive hot path. *)
  val walkerBudgetMs = 1500

  fun logStderr s = (TextIO.output (TextIO.stdErr, s); TextIO.flushOut TextIO.stdErr)

  (* Runs `f` with the calling thread set to `private_interrupts`
     (InterruptAsynchOnce), so the canary's `Thread.interrupt` lands
     asynchronously at the next safe point instead of just setting a
     flag that pure ML never polls.  Under spawnJob's default
     `InterruptSynch`, METIS_TAC would never see the interrupt and
     the walker would run forever — pinning the LSP at 100% CPU per
     stuck query and blocking further auto-follow requests. *)
  (* Returns (result, timedOut) — timedOut = true means the canary
     had to interrupt f() to unstick it, in which case `result` is
     whatever partial state f() returned when its Interrupt handler
     caught. *)
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
  in (r, !timedOut) end

  fun ppGoal (asms, g) = {
    asms = List.map Parse.term_to_string asms,
    goal = Parse.term_to_string g
  }
  (* Render the whole goalstate the way the REPL does — via
     goalFrag's own pretty-printer, driven by the VT100 backend so
     bound / free variables carry ANSI colour escapes.  Clients that
     don't decode ANSI can strip the escapes with an
     `\x1B\[[0-9;]*m` regex. *)
  fun ppState st =
    Lib.with_flag (Parse.current_backend, PPBackEnd.vt100_terminal)
      (HOLPP.pp_to_string 75 goalFrag.pp_goalstate) st
    handle _ => ""

  (* Count Expand/ExpandList steps whose end is strictly before the
     cursor — the step-index the user sits at. *)
  fun stepIndex (steps, cursor) = let
    fun go [] n = n
      | go (TacticSteps.Expand (_, e) :: rest) n =
          if cursor < e then n else go rest (n + 1)
      | go (TacticSteps.ExpandList (_, e) :: rest) n =
          if cursor < e then n else go rest (n + 1)
      | go (_ :: rest) n = go rest n
    in go steps 0 end
in

val () = LSPExtension.goalStateAtPos :=
  (fn ({plugins, ...}: LSPExtension.hover_context,
       {name, quote, quoteStart, tacText, tacStart, cursor}
         : LSPExtension.theorem_context) => let
    val initialGoal = Lib.total Parse.Term [QUOTE quote]
    val steps = TacticSteps.stepsOfTacText
                  {label = "goal_state", tacText = tacText}
    val tacCursor = cursor - tacStart
    in case (initialGoal, steps) of
         (SOME tm, SOME sts) => let
           val startState = goalFrag.new_goal ([], tm)
           val (finalState, partial) = withTimeout walkerBudgetMs (fn () =>
             TacticWalker.walkTo {
               plugins = plugins, theoremName = name,
               theoremStart = quoteStart,
               tacText = tacText, startState = startState,
               steps = sts, cursor = tacCursor})
           in SOME {theorem = name, step = stepIndex (sts, tacCursor),
                    goals = List.map ppGoal (goalFrag.top_goals finalState),
                    pretty = ppState finalState, partial = partial}
           end
       | (SOME tm, NONE) => let
           (* Parser gave us no steps — fall back to the initial goal. *)
           val startState = goalFrag.new_goal ([], tm)
           in SOME {theorem = name, step = 0,
                    goals = [{asms = [], goal = Parse.term_to_string tm}],
                    pretty = ppState startState, partial = false}
           end
       | _ => NONE
    end)

end;
