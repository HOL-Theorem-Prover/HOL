(* LSPExtension.goalStateAtPos: given the enclosing Theorem's
   statement quote and tactic body, walk the tactic stepwise via
   goalFrag and return the goal-state at the cursor. *)

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

  fun ppGoal (asms, g) = {
    asms = List.map Parse.term_to_string asms,
    goal = Parse.term_to_string g
  }
  fun ppState st =
    Lib.with_flag (Parse.current_backend, PPBackEnd.vt100_terminal)
      (HOLPP.pp_to_string 75 goalFrag.pp_goalstate) st
    handle _ => ""

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
    | FAtom (LSelectGoal span) =>
        "Selector `>~ ["
        ^ String.substring (tacText, #1 span, #2 span - #1 span)
        ^ "]` found no matching subgoal"
    | FAtom (LSelectGoals span) =>
        "Selector `>>~ ["
        ^ String.substring (tacText, #1 span, #2 span - #1 span)
        ^ "]` found no matching subgoal"
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
    | FBracket _  => "Bracket failed"
    | FMBracket _ => "Bracket failed"

  fun failRange tacStart frag = case frag of
      FAtom te =>
        Option.map (fn (s, e) => (tacStart + s, tacStart + e))
                   (TacticSteps.atomSpan te)
    | _ => NONE
in

val () = LSPExtension.goalStateAtPos :=
  (fn ({plugins, ...}: LSPExtension.hover_context,
       {name, quote, quoteStart, tacText, tacStart, cursor}
         : LSPExtension.theorem_context) => let
    val initialGoal = Lib.total Parse.Term [QUOTE quote]
    val frags = TacticSteps.fragsOfTacText
                  {label = "goal_state", tacText = tacText}
    val tacCursor = cursor - tacStart
    in case (initialGoal, frags) of
         (SOME tm, SOME fs) => let
           val startState = goalFrag.new_goal ([], tm)
           val step = stepIndex (fs, tacCursor)
           in case withTimeout walkerBudgetMs (fn () =>
                    TacticWalker.walkTo {
                      plugins = plugins, theoremName = name,
                      theoremStart = quoteStart,
                      tacText = tacText, startState = startState,
                      frags = fs, cursor = tacCursor}) of
                NONE => SOME
                  {theorem = name, step = step,
                   goals = [], pretty = "",
                   error = SOME ("walker timed out (>"
                                 ^ LargeInt.toString walkerBudgetMs ^ "ms)"),
                   failedRange = NONE}
              | SOME {state, failedAt} => SOME
                  {theorem = name, step = step,
                   goals = List.map ppGoal (goalFrag.top_goals state),
                   pretty = ppState state,
                   error = Option.map (failMsg tacText) failedAt,
                   failedRange =
                     Option.mapPartial (failRange tacStart) failedAt}
           end
       | (SOME tm, NONE) => let
           val startState = goalFrag.new_goal ([], tm)
           in SOME {theorem = name, step = 0,
                    goals = [{asms = [], goal = Parse.term_to_string tm}],
                    pretty = ppState startState, error = NONE,
                    failedRange = NONE}
           end
       | _ => NONE
    end)

end;
