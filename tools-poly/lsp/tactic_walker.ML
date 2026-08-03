(* Interpret a TacticSteps.step stream against a starting
   goalFrag.goalstate, applying each step and returning the state at
   the cursor's step index.  The interpreter is decoupled from the
   compile — it runs on demand, driven by the cursor. *)

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
     apply, returning the last successful state (so the user sees the
     state as it was when their proof stopped working, rather than a
     downstream tactic operating on stale state).

     All byte offsets (`steps` spans, `cursor`) are relative to
     `tacText`. *)
  val walkTo : {
    tacText: string,
    startState: goalFrag.goalstate,
    steps: TacticSteps.step list,
    cursor: int
  } -> goalFrag.goalstate
end = struct

val holder : Abbrev.tactic option ref = ref NONE

fun compileTactic src = let
  val wrapped = "TacticWalker.holder := SOME (" ^ src ^ ");"
  val i = ref 0
  val n = String.size wrapped
  fun read () = if !i >= n then NONE
                else SOME (String.sub (wrapped, !i)) before i := !i + 1
  fun swallow _ = ()
  val () = holder := NONE
  (* Resolve identifiers via the LSP's file namespace layer (which
     wraps PolyML.globalNameSpace) — same layer the LSP's normal
     compile uses, so identifiers visible to hover are visible here. *)
  val _ = PolyML.compiler
             (read, [PolyML.Compiler.CPErrorMessageProc swallow,
                     PolyML.Compiler.CPNameSpace LSPNameSpace.fileNS]) ()
          handle _ => ()
  in !holder end

fun try f state = SOME (f state) handle _ => NONE

fun expandSrc tacText (s, e) state =
  case compileTactic (String.substring (tacText, s, e - s)) of
    NONE => NONE
  | SOME tac => try (goalFrag.expand tac) state

fun applyStep tacText step state = case step of
    TacticSteps.Expand span     => expandSrc tacText span state
  | TacticSteps.ExpandList span => expandSrc tacText span state
  | TacticSteps.OpenParen   => try goalFrag.open_paren   state
  | TacticSteps.CloseParen  => try goalFrag.close_paren  state
  | TacticSteps.OpenThen1   => try goalFrag.open_then1   state
  | TacticSteps.OpenFirst   => try goalFrag.open_first   state
  | TacticSteps.NextFirst   => try goalFrag.next_first   state
  | TacticSteps.CloseFirst  => try goalFrag.close_first  state
  | TacticSteps.OpenRepeat  => try goalFrag.open_repeat  state
  | TacticSteps.CloseRepeat => try goalFrag.close_repeat state
  | TacticSteps.OpenNthGoal n => try (goalFrag.open_nth_goal n) state

fun walkTo {tacText, startState, steps, cursor} = let
  fun loop [] state = state
    | loop (step :: rest) state = let
        val stopHere = case step of
            TacticSteps.Expand (_, e)     => cursor < e
          | TacticSteps.ExpandList (_, e) => cursor < e
          | _ => false
        in if stopHere then state
           else case applyStep tacText step state of
                  NONE => state  (* step failed — halt, keep last good state *)
                | SOME newState => loop rest newState
        end
  in loop steps startState end

end;
