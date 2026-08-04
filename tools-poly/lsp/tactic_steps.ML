(* Compile a Theorem's tactic body (HOLSourceAST.exp) into a step
   stream for the goalFrag interpreter.  `THENL […]` is opaque for
   now; sub-branch stepping is a follow-up. *)

structure TacticSteps :> sig
  (* Every step carries a byte position that says "the walker halts
     when the cursor is strictly before this".  For an Expand it is
     the end of the tactic's textual span; for structural markers it
     is the position of the operator that induces the marker (e.g.
     the `>-` for OpenThen1 that opens the THEN1 branch, or the end
     of the branch for CloseParen that closes it).  Without this
     position markers would always be applied regardless of cursor,
     which produces a state focused into a subgoal even when the
     cursor is still before the split operator. *)
  datatype step =
      Expand of int * int           (* byte-range of an atomic tactic *)
    | ExpandList of int * int       (* THENL / MAP_EVERY — opaque for now *)
    | OpenParen of int | CloseParen of int
    | OpenThen1 of int              (* >- / THEN1 *)
    | OpenFirst of int | NextFirst of int | CloseFirst of int
    | OpenRepeat of int | CloseRepeat of int
    | OpenNthGoal of int * int      (* n, activation byte *)
  val compileToSteps: HOLSourceAST.exp -> step list

  (* Byte position at/after which the walker should apply the step —
     equivalently, the walker stops when `cursor < stopPos`.  For
     Expand/ExpandList this is the end of the span; for markers it
     is the position they were annotated with. *)
  val stopPos: step -> int

  (* Parse a raw proof-body source (the text between `Proof` and
     `QED`) via a synthesised `Theorem hol_lsp_wrap: T Proof <text>
     QED` wrapper, returning the parsed tactic expression.  `label`
     is passed through to the parser for diagnostics.  Spans on
     the returned exp are in tacText-relative bytes (the wrapper
     prefix has already been accounted for). *)
  val parseTacText:
    {label: string, tacText: string} -> HOLSourceAST.exp option

  (* Convenience: parseTacText + compileToSteps + span shift so
     callers get tacText-coord steps in one call. *)
  val stepsOfTacText:
    {label: string, tacText: string} -> step list option
end = struct

open HOLSourceAST

datatype step =
    Expand of int * int
  | ExpandList of int * int
  | OpenParen of int | CloseParen of int
  | OpenThen1 of int
  | OpenFirst of int | NextFirst of int | CloseFirst of int
  | OpenRepeat of int | CloseRepeat of int
  | OpenNthGoal of int * int

fun stopPos (Expand (_, e))         = e
  | stopPos (ExpandList (_, e))     = e
  | stopPos (OpenParen p)           = p
  | stopPos (CloseParen p)          = p
  | stopPos (OpenThen1 p)           = p
  | stopPos (OpenFirst p)           = p
  | stopPos (NextFirst p)           = p
  | stopPos (CloseFirst p)          = p
  | stopPos (OpenRepeat p)          = p
  | stopPos (CloseRepeat p)         = p
  | stopPos (OpenNthGoal (_, p))    = p

(* Combinator names are matched bare — a qualified `Tactical.THEN`
   parses as an `App` rather than an `Infix` and lands in the generic
   `Expand` branch.  Same for `REPEAT`: only the unqualified form is
   recognised as a step opener. *)
fun then1Steps opPos left right = let val (_, rightEnd) = expSpan right in
  compileToSteps left @ [OpenThen1 opPos]
                      @ compileToSteps right @ [CloseParen rightEnd]
  end
and compileToSteps (e: exp) : step list =
  case e of
    Infix {left, id = (opPos, name), right} =>
     (case name of
        "THEN"  => compileToSteps left @ compileToSteps right
      | ">>"    => compileToSteps left @ compileToSteps right
      | ">-"    => then1Steps opPos left right
      | "THEN1" => then1Steps opPos left right
      | "THENL" => [ExpandList (expSpan e)]
      | _       => [Expand (expSpan e)])
  | Parens {exp = e', ...} => compileToSteps e'
  (* Defensive: raw parseDec output has no ExpExpansion, but a
     post-expansion feed could deliver one. *)
  | ExpExpansion {orig, ...} => compileToSteps orig
  | _ => [Expand (expSpan e)]
  (* `REPEAT tac` is treated as one atomic Expand — decomposing into
     open_repeat / expand / close_repeat runs the body just ONCE, not
     iteratively, which is a semantic error.  goalFrag can't drive a
     REPEAT one-iteration-at-a-time without more machinery.  Same for
     any App(Ident, …) we don't recognise: run as-is. *)

val wrapPrefix = "Theorem hol_lsp_wrap: T\nProof\n"
val wrapPrefixLen = String.size wrapPrefix

fun parseTacText {label, tacText} = let
  val src = wrapPrefix ^ tacText ^ "\nQED\n"
  val consumed = ref false
  fun read _ = if !consumed then "" else (consumed := true; src)
  fun err _ _ _ = ()
  val {parseDec, ...} =
    HOLSourceParser.parseSML label read err HOLSourceParser.initialScope
  in case parseDec () of
       SOME (HOLTheoremDecl {tac, ...}) => SOME tac
     | _ => NONE
  end

fun shiftStep step = let val d = wrapPrefixLen in case step of
    Expand (s, e)     => Expand (s - d, e - d)
  | ExpandList (s, e) => ExpandList (s - d, e - d)
  | OpenParen p       => OpenParen  (p - d)
  | CloseParen p      => CloseParen (p - d)
  | OpenThen1 p       => OpenThen1  (p - d)
  | OpenFirst p       => OpenFirst  (p - d)
  | NextFirst p       => NextFirst  (p - d)
  | CloseFirst p      => CloseFirst (p - d)
  | OpenRepeat p      => OpenRepeat (p - d)
  | CloseRepeat p     => CloseRepeat (p - d)
  | OpenNthGoal (n, p) => OpenNthGoal (n, p - d)
  end

fun stepsOfTacText args =
  Option.map (List.map shiftStep o compileToSteps) (parseTacText args)

end;

(* Load-time selftest.  Raises Fail on regression, which surfaces as
   a `bin/hol lsp` startup crash and shows up in every Python LSP
   test.  Inline because the LSP init doesn't have access to the
   `testutils` selftest infrastructure. *)
local
  fun parseTac tacText =
    case TacticSteps.parseTacText
           {label = "tactic_steps_selftest", tacText = tacText} of
      SOME tac => tac
    | NONE => raise Fail ("parseTac: no HOLTheoremDecl in " ^ tacText)
  fun shape [] = ""
    | shape (TacticSteps.Expand _     :: r) = "E" ^ shape r
    | shape (TacticSteps.ExpandList _ :: r) = "L" ^ shape r
    | shape (TacticSteps.OpenParen _   :: r) = "(" ^ shape r
    | shape (TacticSteps.CloseParen _  :: r) = ")" ^ shape r
    | shape (TacticSteps.OpenThen1 _   :: r) = "[" ^ shape r
    | shape (TacticSteps.OpenFirst _   :: r) = "<" ^ shape r
    | shape (TacticSteps.NextFirst _   :: r) = "|" ^ shape r
    | shape (TacticSteps.CloseFirst _  :: r) = ">" ^ shape r
    | shape (TacticSteps.OpenRepeat _  :: r) = "R" ^ shape r
    | shape (TacticSteps.CloseRepeat _ :: r) = "r" ^ shape r
    | shape (TacticSteps.OpenNthGoal _ :: r) = "N" ^ shape r
  fun check name tacText expected = let
    val steps = TacticSteps.compileToSteps (parseTac tacText)
    val got = shape steps
    in if got = expected then ()
       else raise Fail ("TacticSteps selftest [" ^ name ^ "]: expected "
                        ^ expected ^ ", got " ^ got
                        ^ " for tactic: " ^ tacText)
    end
in
  val _ = check "single leaf"      "ALL_TAC"                     "E"
  val _ = check "THEN chain"       "tac1 THEN tac2 THEN tac3"    "EEE"
  val _ = check ">> chain"         "tac1 >> tac2 >> tac3"        "EEE"
  val _ = check ">- nested parens" "tac1 >- (a >> b) >- (c >> d)"
                                                                 "E[EE)[EE)"
  val _ = check "REPEAT atomic"    "REPEAT (tac1 >> tac2)"       "E"
  val _ = check "nested parens"    "((tac1))"                    "E"
  val _ = check "THENL opaque"     "tac1 THENL [b1, b2, b3]"     "L"
end;
