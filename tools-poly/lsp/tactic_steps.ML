(* Compile a Theorem's tactic body (HOLSourceAST.exp) into a step
   stream for the goalFrag interpreter.  `THENL […]` is opaque for
   now; sub-branch stepping is a follow-up. *)

structure TacticSteps :> sig
  datatype step =
      Expand of int * int           (* byte-range of an atomic tactic *)
    | ExpandList of int * int       (* THENL / MAP_EVERY — opaque for now *)
    | OpenParen | CloseParen
    | OpenThen1                     (* >- / THEN1 *)
    | OpenFirst | NextFirst | CloseFirst  (* ORELSE / FIRST — reserved *)
    | OpenRepeat | CloseRepeat
    | OpenNthGoal of int            (* NTH_GOAL n — reserved *)
  val compileToSteps: HOLSourceAST.exp -> step list

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
  | OpenParen | CloseParen
  | OpenThen1
  | OpenFirst | NextFirst | CloseFirst
  | OpenRepeat | CloseRepeat
  | OpenNthGoal of int

(* Combinator names are matched bare — a qualified `Tactical.THEN`
   parses as an `App` rather than an `Infix` and lands in the generic
   `Expand` branch.  Same for `REPEAT`: only the unqualified form is
   recognised as a step opener. *)
fun compileToSteps (e: exp) : step list =
  case e of
    Infix {left, id = (_, name), right} =>
     (case name of
        "THEN"  => compileToSteps left @ compileToSteps right
      | ">>"    => compileToSteps left @ compileToSteps right
      | ">-"    =>
          compileToSteps left @ [OpenThen1] @ compileToSteps right @ [CloseParen]
      | "THEN1" =>
          compileToSteps left @ [OpenThen1] @ compileToSteps right @ [CloseParen]
      | "THENL" => [ExpandList (expSpan e)]
      | _       => [Expand (expSpan e)])
  | Parens {exp = e', ...} => compileToSteps e'
  (* Defensive: raw parseDec output has no ExpExpansion, but a
     post-expansion feed could deliver one. *)
  | ExpExpansion {orig, ...} => compileToSteps orig
  | App (Ident {id = (_, "REPEAT"), ...}, body) =>
      [OpenRepeat] @ compileToSteps body @ [CloseRepeat]
  | _ => [Expand (expSpan e)]

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

fun shiftStep step = case step of
    Expand (s, e)     => Expand (s - wrapPrefixLen, e - wrapPrefixLen)
  | ExpandList (s, e) => ExpandList (s - wrapPrefixLen, e - wrapPrefixLen)
  | OpenParen   => OpenParen
  | CloseParen  => CloseParen
  | OpenThen1   => OpenThen1
  | OpenFirst   => OpenFirst
  | NextFirst   => NextFirst
  | CloseFirst  => CloseFirst
  | OpenRepeat  => OpenRepeat
  | CloseRepeat => CloseRepeat
  | OpenNthGoal n => OpenNthGoal n

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
    | shape (TacticSteps.OpenParen    :: r) = "(" ^ shape r
    | shape (TacticSteps.CloseParen   :: r) = ")" ^ shape r
    | shape (TacticSteps.OpenThen1    :: r) = "[" ^ shape r
    | shape (TacticSteps.OpenFirst    :: r) = "<" ^ shape r
    | shape (TacticSteps.NextFirst    :: r) = "|" ^ shape r
    | shape (TacticSteps.CloseFirst   :: r) = ">" ^ shape r
    | shape (TacticSteps.OpenRepeat   :: r) = "R" ^ shape r
    | shape (TacticSteps.CloseRepeat  :: r) = "r" ^ shape r
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
  val _ = check "REPEAT compound"  "REPEAT (tac1 >> tac2)"       "REEr"
  val _ = check "nested parens"    "((tac1))"                    "E"
  val _ = check "THENL opaque"     "tac1 THENL [b1, b2, b3]"     "L"
end;
