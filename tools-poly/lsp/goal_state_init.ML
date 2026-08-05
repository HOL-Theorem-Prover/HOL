(* LSPExtension.goalStateAtPos: given the enclosing Theorem's
   statement quote and tactic body, walk the tactic stepwise via
   goalFrag and return the goal-state at the cursor. *)

local
  (* Wall-clock budget for the walker.  Users routinely park their
     cursor past the last tactic in a Proof block; that closer is
     often expensive (METIS_TAC, DECIDE_TAC, …), and without a budget
     each auto-follow tick spawns a fresh walker that runs the whole
     tactic — the LSP ends up pinned at 100% CPU per stuck query.

     The canary Thread.interrupts the walker at the budget.  For the
     interrupt to actually land inside pure ML like METIS_TAC we run
     under `private_interrupts` (InterruptAsynchOnce) — spawnJob's
     default (InterruptSynch) only fires interrupts at explicit
     `Thread.testInterrupt` polls, which HOL tactics don't do.

     `src/portableML/poly/concurrent/Timeout.sml` implements the same
     shape properly (Event_Timer + race-safe cancel) but isn't linked
     into the LSP heap. *)
  val walkerBudgetMs = 1500

  fun logStderr s =
    (TextIO.output (TextIO.stdErr, s); TextIO.flushOut TextIO.stdErr)

  (* Returns SOME (f ()) when f completed within the budget, NONE
     when the canary had to interrupt it — a mid-walk partial state
     is complete for its own step but wrong for the cursor's step,
     so callers surface it as "no goal-state" rather than misleading
     the user with stale content. *)
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
           in case withTimeout walkerBudgetMs (fn () =>
                    TacticWalker.walkTo {
                      plugins = plugins, theoremName = name,
                      theoremStart = quoteStart,
                      tacText = tacText, startState = startState,
                      steps = sts, cursor = tacCursor}) of
                NONE => NONE
              | SOME finalState => SOME
                  {theorem = name, step = stepIndex (sts, tacCursor),
                   goals = List.map ppGoal (goalFrag.top_goals finalState),
                   pretty = ppState finalState}
           end
       | (SOME tm, NONE) => let
           val startState = goalFrag.new_goal ([], tm)
           in SOME {theorem = name, step = 0,
                    goals = [{asms = [], goal = Parse.term_to_string tm}],
                    pretty = ppState startState}
           end
       | _ => NONE
    end)

end;
