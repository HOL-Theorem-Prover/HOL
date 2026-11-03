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

(* A span is clamped to the body it indexes, which is what every
   consumer already assumes of it.  An unterminated string, character
   literal or HOL quotation makes the lexer run to the end of the
   *wrapped* source, so the span recorded for that leaf covers the
   synthetic `QED' too: measured here, `simp["abc]' is ten characters
   and comes back spanning fifteen.  Unclamped, the walker's `textAt'
   is then an out-of-range `String.substring' -- and several of its
   call sites sit outside the `Portable.total' guarding their step --
   while `failedRange' would ask the client to squiggle past the end of
   the proof.

   Clamping where the spans are shifted keeps every consumer honest at
   once; `linearize' runs afterwards, so the fragment opens carrying
   spans of their own inherit it too. *)
fun fragsOfTacText (args as {tacText, ...}) =
  case parseTacText args of
    NONE => NONE
  | SOME tac_ast => let
      val d = wrapPrefixLen
      val n = String.size tacText
      fun clamp (s, e) = let
        val s' = Int.max (0, Int.min (s - d, n))
        val e' = Int.max (s', Int.min (e - d, n))
        in (s', e') end
      val shifted = TacticParse.mapTacExpr {
          start = fn _ => clamp,
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
    | open_ch (FOpenThen1 _)  = "["
    | open_ch (FOpenBy _)     = "B"
    | open_ch (FOpenSufficesBy _) = "U"
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
  (* Every span a consumer will slice `tacText' with has to index it.
     The walker's `textAt' and the client's `failedRange' both do, and
     an unterminated string, character literal or quotation used to run
     the lexer past the body and into the synthetic `QED'. *)
  fun checkSpans name tacText = let
    val n = String.size tacText
    fun bad what (s, e) =
      if s < 0 orelse e < s orelse e > n then
        raise Fail ("TacticSteps selftest [" ^ name ^ "]: " ^ what
                    ^ " span (" ^ Int.toString s ^ "," ^ Int.toString e
                    ^ ") outside body of size " ^ Int.toString n
                    ^ " for tactic: " ^ tacText)
      else ()
    fun atom te = case TacticSteps.atomSpan te of
                      SOME sp => bad "atom" sp
                    | NONE => ()
    fun opn ok = case ok of
                     FOpenThen1 sp => bad "THEN1" sp
                   | FOpenBy (q, sp) => (bad "by-quote" q; bad "by" sp)
                   | FOpenSufficesBy (q, sp) =>
                       (bad "suffices_by-quote" q; bad "suffices_by" sp)
                   | _ => ()
    fun walk [] = ()
      | walk (FAtom te :: r) = (atom te; walk r)
      | walk (FFOpen o' :: r) = (opn o'; walk r)
      | walk (FGroup (_, fs) :: r) = (walk fs; walk r)
      | walk (FBracket (o', fs, _, _) :: r) = (opn o'; walk fs; walk r)
      | walk (FMBracket (o', _, _, secs, _) :: r) =
          (opn o'; List.app walk secs; walk r)
      | walk (_ :: r) = walk r
    in walk (parseFrags tacText) end
  (* The other half of the same question.  `checkSpans' asks whether
     every span indexes the body; this asks whether the plan reaches
     the end of it.  A plan that stops early is the dangerous kind of
     wrong: the walker runs out of steps and the block reads as a
     finished proof, which is a confident answer rather than a
     missing one.

     Full byte coverage is not an invariant in general -- a body may
     end in a comment or in whitespace, which no step spans -- so the
     cases below are chosen to end in a tactic token, and `expected'
     is the byte they must reach.  The delimiters inside strings,
     quotations and comments are the point: a scan that took them for
     real delimiters would stop at one and still answer. *)
  fun covers name tacText = let
    val n = String.size tacText
    fun te_end te = case topSpan te of SOME (_, e) => e | NONE => 0
    fun fe (f, acc) =
      case f of
          FAtom te => Int.max (acc, Int.max (te_end te,
                        getOpt (TacticSteps.atomEndByte te, 0)))
        | FGroup ((_, e), fs) => List.foldl fe (Int.max (acc, e)) fs
        | FBracket (_, fs, _, te) =>
            List.foldl fe (Int.max (acc, te_end te)) fs
        | FMBracket (_, _, _, secs, te) =>
            List.foldl (fn (fs, a) => List.foldl fe a fs)
                       (Int.max (acc, te_end te)) secs
        | _ => acc
    val reached = List.foldl fe 0 (parseFrags tacText)
    in if reached >= n then ()
       else raise Fail ("TacticSteps selftest [" ^ name
                        ^ "]: the step plan stops at " ^ Int.toString reached
                        ^ " of " ^ Int.toString n
                        ^ " bytes, so the walker would read the tail as a"
                        ^ " finished proof -- tactic: " ^ tacText)
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
  val _ = check "by block"         "`n < 10` by (rw[] >> simp[])" "BEE)"
  val _ = check "suffices_by"      "`n < 10` suffices_by rw[]"    "UE)"
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
  (* A body being typed in: the closing delimiter is not there yet.
     The lexer runs to the end of the wrapped source, so these are the
     shapes whose spans used to cover the synthetic `QED'. *)
  val _ = checkSpans "unterminated string"  "simp[\"abc]"
  val _ = checkSpans "unterminated string mid-chain" "rw[] >> simp[\"abc]"
  val _ = checkSpans "unterminated quote"   "`n < 10 by simp[]"
  val _ = checkSpans "unterminated char"    "simp[#\"a]"
  val _ = checkSpans "unclosed comment"     "simp[] (* oops"
  val _ = checkSpans "unclosed paren"       "tac1 >- (a >> b"
  val _ = checkSpans "unclosed by-paren"    "`n < 10` by (rw[]"
  val _ = checkSpans "stray close paren"    "tac1 >> tac2)"
  val _ = checkSpans "balanced control"     "tac1 >- (a >> b) >- (c >> d)"
  (* A delimiter that is not a delimiter.  Each of these ends in a
     tactic token, so the plan has to reach the last byte. *)
  val _ = covers "plain chain"        "rpt strip_tac >> simp[]"
  val _ = covers "nested parens"      "rpt strip_tac >> (simp[] >> simp[])"
  val _ = covers "close bracket in an SML string"
                                      "rw[] >> print_tac \"]\""
  val _ = covers "open bracket in an SML string"
                                      "rw[] >> print_tac \"[\""
  val _ = covers "close paren in an SML string"
                                      "rw[] >> print_tac \")\""
  val _ = covers "open paren in an SML string"
                                      "rw[] >> print_tac \"(\""
  val _ = covers "close bracket in a quotation"
                                      "`STRLEN \"]\" = 1` by simp[] >> rw[]"
  val _ = covers "close paren in a quotation"
                                      "`STRLEN \")\" = 1` by simp[] >> rw[]"
  val _ = covers "bracket in a comment" "rpt strip_tac (* ] *) >> simp[]"
  val _ = covers "paren in a comment"   "rpt strip_tac (* ( *) >> simp[]"
  val _ = covers "quotation argument"
                   "rpt strip_tac >> qexists_tac `a:num` >> simp[]"
end;
