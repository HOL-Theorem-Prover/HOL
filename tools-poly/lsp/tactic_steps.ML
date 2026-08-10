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
    | ExpandList of int * int       (* fallback when THENL's RHS isn't
                                       a literal list (variable, App, …) *)
    (* `>~ pats` / `>>~ pats` split as [left steps, GoalSelect (opStart,
       rightEnd)].  The right operand is a term-quote list, not a
       tactic, so the walker can't compile `>~ [pat]` as a leaf;
       instead it synthesises `"ALL_TAC " ^ tacText[opStart..rightEnd]`,
       which is a valid tactic that applies the goal-selector on the
       current focus. *)
    | GoalSelect of int * int
    | OpenParen of int | CloseParen of int
    | OpenThen1 of int              (* >- / THEN1 *)
    | OpenFirst of int | NextFirst of int | CloseFirst of int
    | OpenRepeat of int | CloseRepeat of int
    | OpenNthGoal of int * int      (* n, activation byte *)
    (* `THENL [b1, b2, …, bn]` / `>| [b1, …]` — the walker splits into
       inner-branch steps.  `OpenTacsToLT` at the `[` focuses the first
       subgoal; `NextTacsToLT` at each `,` completes the previous
       branch and focuses the next; the trailing `CloseParen` at the
       list's stop position finalises the list-tactic. *)
    | OpenTacsToLT of int
    | NextTacsToLT of int
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
  | GoalSelect of int * int
  | OpenParen of int | CloseParen of int
  | OpenThen1 of int
  | OpenFirst of int | NextFirst of int | CloseFirst of int
  | OpenRepeat of int | CloseRepeat of int
  | OpenNthGoal of int * int
  | OpenTacsToLT of int
  | NextTacsToLT of int

fun stopPos (Expand (_, e))         = e
  | stopPos (ExpandList (_, e))     = e
  | stopPos (GoalSelect (_, e))     = e
  | stopPos (OpenParen p)           = p
  | stopPos (CloseParen p)          = p
  | stopPos (OpenThen1 p)           = p
  | stopPos (OpenFirst p)           = p
  | stopPos (NextFirst p)           = p
  | stopPos (CloseFirst p)          = p
  | stopPos (OpenRepeat p)          = p
  | stopPos (CloseRepeat p)         = p
  | stopPos (OpenNthGoal (_, p))    = p
  | stopPos (OpenTacsToLT p)        = p
  | stopPos (NextTacsToLT p)        = p

(* Combinator names are matched bare — a qualified `Tactical.THEN`
   parses as an `App` rather than an `Infix` and lands in the generic
   `Expand` branch.  Same for `REPEAT`: only the unqualified form is
   recognised as a step opener. *)
fun then1Steps opPos left right = let val (_, rightEnd) = expSpan right in
  compileToSteps left @ [OpenThen1 opPos]
                      @ compileToSteps right @ [CloseParen rightEnd]
  end
(* Descend into the `[b1, b2, …, bn]` right-hand side of THENL / `>|`.
   Emits OpenTacsToLT at `[`, walks each branch's own step stream,
   inserts NextTacsToLT at each `,` between branches, and a trailing
   CloseParen at the list's stop position.  If the RHS isn't a
   literal list -- e.g. `THENL bs` where `bs` is a variable, or an
   `App` that produces a list -- falls back to a single opaque
   ExpandList step so the walker halts cleanly at the whole-list
   boundary. *)
and thenlSteps left right =
  let val leftSteps = compileToSteps left in
  case right of
    List {left = lbracket, elems = {args, seps, ...}, stop, ...} =>
      let
        (* Zip the argument list with the separator list.  For a
           normal `[b1, b2, b3]` seps has n-1 entries (SOME p per `,`);
           a trailing sep or a synthetic list can also occur, so we
           tolerate both shortfall and surplus. *)
        fun walk [] _ = []
          | walk [b] _ = compileToSteps b
          | walk (b :: bs) (SOME p :: ss) =
              compileToSteps b @ [NextTacsToLT p] @ walk bs ss
          | walk (b :: bs) (NONE :: ss) =
              (* Parse-error-repaired missing sep.  Use end-of-`b`
                 as the activation so the walker still splits. *)
              let val (_, bEnd) = expSpan b in
              compileToSteps b @ [NextTacsToLT bEnd] @ walk bs ss
              end
          | walk (b :: bs) [] =
              (* Fewer seps than we have gaps.  Same fallback: end
                 of the current branch. *)
              let val (_, bEnd) = expSpan b in
              compileToSteps b @ [NextTacsToLT bEnd] @ walk bs []
              end
      in
        leftSteps @ [OpenTacsToLT lbracket] @ walk args seps
                  @ [CloseParen stop]
      end
  | _ => leftSteps @ [ExpandList (expSpan right)]
  end
and compileToSteps (e: exp) : step list =
  case e of
    Infix {left, id = (opPos, name), right} =>
     (case name of
        "THEN"  => compileToSteps left @ compileToSteps right
      | ">>"    => compileToSteps left @ compileToSteps right
      | "\\\\"  => compileToSteps left @ compileToSteps right
      | ">-"    => then1Steps opPos left right
      | "THEN1" => then1Steps opPos left right
      | "THENL" => thenlSteps left right
      | ">|"    => thenlSteps left right
      (* `>~ pats` / `>>~ pats` — right operand is a term-quote list,
         not a tactic.  Split so cursor between `left` and the
         selector sees post-left state; the selector then applies as
         a synthesised `ALL_TAC >~ pats` leaf via GoalSelect. *)
      | ">~"    =>
          let val (_, rightEnd) = expSpan right in
            compileToSteps left @ [GoalSelect (opPos, rightEnd)]
          end
      | ">>~"   =>
          let val (_, rightEnd) = expSpan right in
            compileToSteps left @ [GoalSelect (opPos, rightEnd)]
          end
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
  | GoalSelect (s, e) => GoalSelect (s - d, e - d)
  | OpenParen p       => OpenParen  (p - d)
  | CloseParen p      => CloseParen (p - d)
  | OpenThen1 p       => OpenThen1  (p - d)
  | OpenFirst p       => OpenFirst  (p - d)
  | NextFirst p       => NextFirst  (p - d)
  | CloseFirst p      => CloseFirst (p - d)
  | OpenRepeat p      => OpenRepeat (p - d)
  | CloseRepeat p     => CloseRepeat (p - d)
  | OpenNthGoal (n, p) => OpenNthGoal (n, p - d)
  | OpenTacsToLT p    => OpenTacsToLT (p - d)
  | NextTacsToLT p    => NextTacsToLT (p - d)
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
    | shape (TacticSteps.Expand _      :: r) = "E" ^ shape r
    | shape (TacticSteps.ExpandList _  :: r) = "L" ^ shape r
    | shape (TacticSteps.GoalSelect _  :: r) = "G" ^ shape r
    | shape (TacticSteps.OpenParen _   :: r) = "(" ^ shape r
    | shape (TacticSteps.CloseParen _  :: r) = ")" ^ shape r
    | shape (TacticSteps.OpenThen1 _   :: r) = "[" ^ shape r
    | shape (TacticSteps.OpenFirst _   :: r) = "<" ^ shape r
    | shape (TacticSteps.NextFirst _   :: r) = "|" ^ shape r
    | shape (TacticSteps.CloseFirst _  :: r) = ">" ^ shape r
    | shape (TacticSteps.OpenRepeat _  :: r) = "R" ^ shape r
    | shape (TacticSteps.CloseRepeat _ :: r) = "r" ^ shape r
    | shape (TacticSteps.OpenNthGoal _ :: r) = "N" ^ shape r
    | shape (TacticSteps.OpenTacsToLT _ :: r) = "T" ^ shape r
    | shape (TacticSteps.NextTacsToLT _ :: r) = ";" ^ shape r
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
  val _ = check "\\\\ chain"       "tac1 \\\\ tac2 \\\\ tac3"    "EEE"
  val _ = check ">- nested parens" "tac1 >- (a >> b) >- (c >> d)"
                                                                 "E[EE)[EE)"
  val _ = check ">- with \\\\"     "tac1 >- (a \\\\ b \\\\ c)"   "E[EEE)"
  val _ = check "REPEAT atomic"    "REPEAT (tac1 >> tac2)"       "E"
  val _ = check "nested parens"    "((tac1))"                    "E"
  val _ = check "THENL branches"   "tac1 THENL [b1, b2, b3]"     "ETE;E;E)"
  val _ = check ">| branches"      "tac1 >| [b1, b2, b3]"        "ETE;E;E)"
  val _ = check "THENL single"     "tac1 THENL [b1]"             "ETE)"
  val _ = check "THENL var-rhs"    "tac1 THENL bs"               "EL"
  val _ = check ">~ selector"      "tac1 >~ [`P`]"               "EG"
  val _ = check ">>~ selector"     "tac1 >>~ [`P`, `Q`]"         "EG"
  val _ = check ">~ then >>"       "tac1 >~ [`P`] >> tac2"       "EGE"
end;
