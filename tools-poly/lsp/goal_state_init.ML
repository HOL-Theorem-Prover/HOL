(* LSPExtension.goalStateAtPos: given the enclosing Theorem's
   statement quote and tactic body, walk the tactic stepwise via
   goalFrag and return the goal-state at the cursor. *)

local
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
           val finalState = TacticWalker.walkTo {
             plugins = plugins, theoremName = name,
             theoremStart = quoteStart,
             tacText = tacText, startState = startState,
             steps = sts, cursor = tacCursor}
           in SOME {theorem = name, step = stepIndex (sts, tacCursor),
                    goals = List.map ppGoal (goalFrag.top_goals finalState),
                    pretty = ppState finalState}
           end
       | (SOME tm, NONE) => let
           (* Parser gave us no steps — fall back to the initial goal. *)
           val startState = goalFrag.new_goal ([], tm)
           in SOME {theorem = name, step = 0,
                    goals = [{asms = [], goal = Parse.term_to_string tm}],
                    pretty = ppState startState}
           end
       | _ => NONE
    end)

end;
