(* Parse a Theorem's tactic body into TacticParse.tac_frag form for
   the goalFrag walker.  TacticParse already elaborates every
   surface sugar (by, suffices_by, tilde-selectors, MapEvery,
   Rename, Repair) so the walker doesn't need its own combinator-
   name matcher. *)

structure TacticSteps :> sig
  (* Full pipeline: wrap the proof body in a synthetic Theorem,
     parse via HOLSourceParser, run TacticParse's surface-sugar
     elaboration, linearize to a tac_frag list with every span
     shifted into tacText-relative coordinates. *)
  val fragsOfTacText:
    {label: string, tacText: string} -> TacticParse.tac_frag list option

  (* Whole source extent of a leaf tac_expr, and its end alone.
     Shared between the walker and the LSP response builder so both
     classify snap-worthy atoms identically. *)
  val atomSpan: (int * int) TacticParse.tac_expr -> (int * int) option
  val atomEndByte: (int * int) TacticParse.tac_expr -> int option
end = struct

val wrapPrefix = "Theorem hol_lsp_wrap: T\nProof\n"
val wrapPrefixLen = String.size wrapPrefix

(* `TacticParse.topSpan' already answers for every leaf whose
   annotation is the whole expression -- including the Opaque family
   and LSelectGoal(s), and NONE for LReverse.  Only the four below
   annotate an operand instead, so only they need assembling. *)
fun atomSpan te = let
  open TacticParse
  (* MapEvery/MapFirst carry the span of the mapped function, not of
     the whole call, so end the atom at its last argument -- otherwise
     a cursor sitting in the argument list already counts as past the
     atom and fires it early.  The closing bracket stays outside the
     extent: the call's own span isn't recorded in the tree. *)
  fun lastArgEnd dflt args =
    List.foldl (fn (a, e) => case topSpan a of SOME (_, e') => e' | NONE => e)
               dflt args
in case te of
    Subgoal span => SOME span
  | Rename span  => SOME span
  | MapEvery ((s, e), args)
  | MapFirst ((s, e), args) => SOME (s, lastArgEnd e args)
  | _ => topSpan te
end

val atomEndByte = Option.map #2 o atomSpan

fun parseTacText {label, tacText} = let
  val src = wrapPrefix ^ tacText ^ "\nQED\n"
  val consumed = ref false
  fun read _ = if !consumed then "" else (consumed := true; src)
  fun err _ _ _ = ()
  val {parseDec, ...} =
    HOLSourceParser.parseSML label read err HOLSourceParser.initialScope
  in case parseDec () of
       SOME (HOLSourceAST.HOLTheoremDecl {tac, ...}) => SOME tac
     | _ => NONE
  end

fun fragsOfTacText args =
  case parseTacText args of
    NONE => NONE
  | SOME tac_ast => let
      val d = wrapPrefixLen
      val shifted = TacticParse.mapTacExpr {
          start = fn _ => fn (s, e) => (s - d, e - d),
          stop  = fn _ => fn x => x,
          repair = fn _ => fn _ => () }
        (TacticParse.parseTacticBlock tac_ast)
      (* `fn _ => false` = maximum decomposition; leaves still land
         as FAtom via linearize's own classification. *)
      in SOME (TacticParse.linearize (fn _ => false) shifted) end

end;

(* Load-time selftest -- raises Fail on regression. *)
local
  open TacticParse
  fun parseFrags tacText =
    case TacticSteps.fragsOfTacText
           {label = "tactic_steps_selftest", tacText = tacText} of
      SOME frags => frags
    | NONE => raise Fail ("parseFrags: no HOLTheoremDecl in " ^ tacText)
  fun open_ch FOpen           = "("
    | open_ch FOpenThen1      = "["
    | open_ch FOpenFirst      = "<"
    | open_ch FOpenRepeat     = "R"
    | open_ch FOpenTacsToLT   = "T"
    | open_ch FOpenNullOk     = "K"
    | open_ch (FOpenNthGoal _) = "N"
    | open_ch FOpenLastGoal   = "L"
    | open_ch FOpenHeadGoal   = "H"
    | open_ch (FOpenSplit _)  = "S"
    | open_ch FOpenSelect     = "$"
    | open_ch FOpenFirstLT    = "F"
  fun mid_ch FNextFirst       = "|"
    | mid_ch FNextTacsToLT    = ";"
    | mid_ch FNextSplit       = ","
    | mid_ch FNextSelect      = "~"
  fun close_ch FClose         = ")"
    | close_ch FCloseFirst    = ">"
    | close_ch FCloseRepeat   = "r"
    | close_ch FCloseFirstLT  = "f"
  fun atom_ch te = case te of
      Subgoal _      => "S"
    | LSelectGoal _  => "G"
    | LSelectGoals _ => "g"
    | LReverse       => "V"
    | Rename _       => "N"
    | MapEvery _     => "M"
    | MapFirst _     => "m"
    | _              => "E"
  fun shape [] = ""
    | shape (FAtom te :: r)              = atom_ch te ^ shape r
    | shape (FFOpen o' :: r)             = open_ch o' ^ shape r
    | shape (FFMid m :: r)               = mid_ch m ^ shape r
    | shape (FFClose c :: r)             = close_ch c ^ shape r
    | shape (FGroup (_, fs) :: r)        = shape fs ^ shape r
    | shape (FBracket (o', fs, c, _) :: r) =
        open_ch o' ^ shape fs ^ close_ch c ^ shape r
    | shape (FMBracket (o', m, c, secs, _) :: r) = let
        fun sec [] = ""
          | sec [s] = shape s
          | sec (s :: rest) = shape s ^ mid_ch m ^ sec rest
        in open_ch o' ^ sec secs ^ close_ch c ^ shape r end
  fun check name tacText expected = let
    val got = shape (parseFrags tacText)
    in if got = expected then ()
       else raise Fail ("TacticSteps selftest [" ^ name ^ "]: expected "
                        ^ expected ^ ", got " ^ got
                        ^ " for tactic: " ^ tacText)
    end
in
  val _ = check "single leaf"      "simp[]"                      "E"
  val _ = check "ALL_TAC no-op"    "ALL_TAC"                     ""
  val _ = check "THEN chain"       "tac1 THEN tac2 THEN tac3"    "EEE"
  val _ = check ">> chain"         "tac1 >> tac2 >> tac3"        "EEE"
  val _ = check ">- nested parens" "tac1 >- (a >> b) >- (c >> d)"
                                                                 "E[EE)[EE)"
  val _ = check "REPEAT atomic"    "REPEAT (tac1 >> tac2)"       "REEr"
  val _ = check "nested parens"    "((tac1))"                    "E"
  val _ = check "THENL branches"   "tac1 THENL [b1, b2, b3]"     "EKTE;E;E))"
  val _ = check "THENL single"     "tac1 THENL [b1]"             "EKTE))"
  val _ = check ">~ selector"      "tac1 >~ [`P`]"               "EG"
  val _ = check ">>~ selector"     "tac1 >>~ [`P`, `Q`]"         "Eg"
  val _ = check "by block"         "`n < 10` by (rw[] >> simp[])" "S[EE)"
  val _ = check "suffices_by"      "`n < 10` suffices_by rw[]"    "SV[E)"
  (* MapEvery/MapFirst/Rename are single atoms whose span covers only
     an operand -- the walker reaches them through TacticParse's
     inverse printer, so pin that they stay atoms. *)
  val _ = check "MAP_EVERY"        "MAP_EVERY X_GEN_TAC [`p`, `q`]" "M"
  val _ = check "MAP_FIRST"        "MAP_FIRST ACCEPT_TAC [th1, th2]" "m"
  val _ = check "RENAME_TAC"       "RENAME_TAC [`p` |-> `q`]"     "N"
  (* TRY is ORELSE with an empty second branch: the `|' before the
     closer is what lets a failing inner tactic be absorbed. *)
  val _ = check "TRY"              "TRY tac1"                    "<E|)"
  val _ = check "TRY multi-step"   "TRY (tac1 >> tac2)"          "<EE|)"
  val _ = check "ORELSE"           "tac1 ORELSE tac2"            "<E|E)"
  val _ = check "TRY_LT"           "tac1 THEN_LT TRY_LT (ALLGOALS tac2)"
                                                                 "E<E|>"
end;
