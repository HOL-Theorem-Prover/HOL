(* Slice C: compile a Theorem's tactic body (HOLSourceAST.exp) into a
   step stream for Slice D's goalFrag interpreter.  `THENL […]` is
   opaque for now; sub-branch stepping is a follow-up. *)

structure TacticSteps :> sig
  datatype step =
      Expand of int * int           (* file byte-range of an atomic tactic *)
    | ExpandList of int * int       (* THENL / MAP_EVERY — opaque for now *)
    | OpenParen | CloseParen
    | OpenThen1                     (* >- / THEN1 *)
    | OpenFirst | NextFirst | CloseFirst  (* ORELSE / FIRST — reserved *)
    | OpenRepeat | CloseRepeat
    | OpenNthGoal of int            (* NTH_GOAL n — reserved *)
  val compileToSteps: HOLSourceAST.exp -> step list
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
  (* Defensive: raw parseDec output has no ExpExpansion, but Slice G
     may feed us post-expansion ASTs. *)
  | ExpExpansion {orig, ...} => compileToSteps orig
  | App (Ident {id = (_, "REPEAT"), ...}, body) =>
      [OpenRepeat] @ compileToSteps body @ [CloseRepeat]
  | _ => [Expand (expSpan e)]

end;

(* Load-time selftest.  Raises Fail on regression, which surfaces as
   an `bin/hol lsp` startup crash and shows up in every Python LSP
   test.  Inline because the LSP init doesn't have access to the
   `testutils` selftest infrastructure. *)
local
  open HOLSourceAST
  fun parseTac tacText = let
    val src = "Theorem selftest_thm: T\nProof\n" ^ tacText ^ "\nQED\n"
    val consumed = ref false
    fun read _ = if !consumed then "" else (consumed := true; src)
    fun err _ _ _ = ()
    val {parseDec, ...} =
      HOLSourceParser.parseSML "tactic_steps_selftest" read err
        HOLSourceParser.initialScope
    in case parseDec () of
         SOME (HOLTheoremDecl {tac, ...}) => tac
       | _ => raise Fail ("parseTac: no HOLTheoremDecl in " ^ tacText)
    end
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
