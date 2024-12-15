open Lib Type PP smpp PPBackEnd testutils

val failcount = ref 0
val _ = diemode := Remember failcount

(* -------------------------------------------------------------------------- *)
(* Test code for terminal styles                                              *)
(* -------------------------------------------------------------------------- *)

val color_name_fw_spaces      = "          ";
fun color_name_fw Black       = "Black     "
  | color_name_fw RedBrown    = "RedBrown  "
  | color_name_fw Green       = "Green     "
  | color_name_fw BrownGreen  = "BrownGreen"
  | color_name_fw DarkBlue    = "DarkBlue  "
  | color_name_fw Purple      = "Purple    "
  | color_name_fw BlueGreen   = "BlueGreen "
  | color_name_fw DarkGrey    = "DarkGrey  "
  | color_name_fw LightGrey   = "LightGrey "
  | color_name_fw OrangeRed   = "OrangeRed "
  | color_name_fw VividGreen  = "VividGreen"
  | color_name_fw Yellow      = "Yellow    "
  | color_name_fw Blue        = "Blue      "
  | color_name_fw PinkPurple  = "PinkPurple"
  | color_name_fw LightBlue   = "LightBlue "
  | color_name_fw White       = "White     ";


val color_list =
  [ Black     , RedBrown   , Green      , BrownGreen,
    DarkBlue  , Purple     , BlueGreen  , DarkGrey,
    LightGrey , OrangeRed  , VividGreen , Yellow,
    Blue      , PinkPurple , LightBlue  , White]

val _ = tprint "Basic vt100 style"
val s = HOLPP.pp_to_string
          70
          (fn s => Parse.mlower
                     (#ustyle vt100_terminal [FG Blue] (smpp.add_string s)))
          "should be blue"
val _ = if s = "\027[0;1;34mshould be blue\027[0m" then OK()
        else die "FAILED!";


fun test_terminal test_bg (terminal:t) =
let
   val {add_string, add_xstring, add_newline, add_break,
        ustyle, ublock, ...} = terminal
   fun add_ann_string (s,ann) = add_xstring {s=s,ann=SOME ann,sz=NONE}

   val fg_styles =
          ((" -            "^color_name_fw_spaces), [])::
     map (fn c =>
          ((" - Foreground "^(color_name_fw c)), [FG c])) color_list
   val bold_fg_styles =
     (map (fn (s, styL) => (" -     "^s, styL)) fg_styles)@
     (map (fn (s, styL) => (" - Bold"^s, Bold::styL)) fg_styles)
   val und_fg_styles =
     (map (fn (s, styL) => ("         "^s, styL)) bold_fg_styles)@
     (map (fn (s, styL) => ("Underline"^s, Underline::styL)) bold_fg_styles)

   val full_styles = if not test_bg then und_fg_styles else
     (flatten (
        (map (fn (s, styL) =>
            ((s^" -            "^color_name_fw_spaces), styL)) und_fg_styles)::
         (map (fn c =>
          map (fn (s, styL) =>
            ((s^" - Background "^(color_name_fw c)), (BG c)::styL)) und_fg_styles)
          color_list)))
   val m =
       ublock INCONSISTENT 0 (
         add_string "Terminal testing" >> add_newline >>
         add_string "================" >> add_newline >> add_newline >>

         add_string "Annotations:" >> add_newline >>
         add_string "------------" >> add_newline >>
         add_ann_string ("Bound variable", BV (bool, fn () => ": bool")) >>
         add_newline >>
         add_ann_string ("Free variable", FV (bool, fn () => ": bool")) >>
         add_newline >>
         add_ann_string ("Type variable", TyV) >>
         add_newline >>
         add_ann_string ("TySyn", TySyn (fn () => "TySyn")) >>
         add_newline >>
         add_ann_string ("TyOp", TyOp (fn () => "TyOp")) >>
         add_newline >>
         add_ann_string ("Const", Const {Name = "test-name", Thy = "test-thy",
                                         Ty = (Type.bool, fn () => "bool")}) >>
         add_newline >>
         add_ann_string ("Note", Note "Some note") >>
         add_newline >>

         add_newline >> add_newline >>

         add_string "Basic styles:" >> add_newline >>
         add_string "-------------" >> add_newline >>
         add_string "default style" >> add_newline >>
         ustyle [Bold] (add_string "Bold") >> add_newline >>
         ustyle [Underline] (add_string "Underline") >> add_newline >>
         mapp (fn c => (
                 add_string "Foreground " >>
                 ustyle [FG c] (add_string (color_name_fw c)) >>
                 add_newline))
              color_list >>
         mapp (fn c => (
                add_string "Background " >>
                ustyle [BG c] (add_string (color_name_fw c)) >>
                add_newline)) color_list >>
         add_newline >> add_newline >>

         (if test_bg then
            add_string "All style combinations:" >> add_newline >>
            add_string "------------------------" >> add_newline
          else
            add_string "All style combinations (without background color):" >>
            add_newline >>
            add_string "--------------------------------------------------" >>
            add_newline) >>
         mapp (fn (s, styL) => ustyle styL (add_string s) >> add_newline)
              full_styles >>
         add_newline >> add_newline
       )
in
  HOLPP.prettyPrint (TextIO.print, 75) (Parse.mlower m)
end;


val _ = print "raw terminal\n";
val _ = print "============\n\n";
val _ = test_terminal false (PPBackEnd.raw_terminal);

val _ = print "emacs terminal\n";
val _ = print "==============\n\n";
val _ = test_terminal false (PPBackEnd.emacs_terminal);

val _ = print "vt100 terminal\n";
val _ = print "==============\n\n";
val _ = test_terminal false (PPBackEnd.vt100_terminal);



(* ----------------------------------------------------------------------
    Tests of the base lexer
   ---------------------------------------------------------------------- *)

val _ = print "** Testing basic lexing functionality\n\n"
open base_tokens

exception InternalDie of string
fun idie s = raise InternalDie s

fun quoteToString [QUOTE s] = "`"^s^"`"
  | quoteToString _ = idie "Bad test quotation"

fun test (q, slist) = let
  val _ = tprint ("Testing " ^ quoteToString q)
  fun prs s = "\"" ^ String.toString s ^ "\""
  fun prsl sl = "[" ^ String.concatWith ", " (map prs sl) ^ "]"
in
  require_msg (check_result (equal slist)) prsl
              (map (base_tokens.toString o #1) o qbuf.lex_to_toklist) q
end handle InternalDie s => die s

val _ = app test [(`abc`, ["abc"]),
                  (`12`, ["12"]),
                  (`3.0`, ["3.0"]),
                  (`3.00`, ["3.00"]),
                  (`0xab`, ["171"]),
                  (`12.1`, ["12.1"]),
                  (`12.01`, ["12.01"]),
                  (`12.010`, ["12.010"]),
                  (`(`, ["("]),
                  (`a(a`, ["a(a"]),
                  (`x+y`, ["x+y"]),
                  (`x +y`, ["x", "+y"]),
                  (`x ++ y`, ["x", "++", "y"]),
                  (`x (* *)y`, ["x", "y"]),
                  (`x(**)y`, ["x", "y"]),
                  (`+(**)y`, ["+", "y"]),
                  (`((*x*)`, ["("]),
                  (`+(%*%((*"*)-*foo`,["+(%*%(", "-*foo"]),
                  (`"(*"`, ["BTStrL(\",\"(*\")"]),
                  (`foo$bar`, ["foo$bar"]),
                  (`+foo$bar`, ["+", "foo$bar"]),
                  (`+foo$bar+`, ["+", "foo$bar", "+"])
                 ]

(* tests of the term lexer *)
local
  open term_tokens
  fun prtoks l =
      "["^ String.concatWith ", " (map (toString (fn _ => "()")) l) ^ "]"
  val testf = lextest ["--b->", "=β=>₁", "(<", ">)", "-->"]

fun test (s, toklist : unit term_token list) = let
  val _ = tprint ("Term token testing " ^ Lib.quote (String.toString s))
in
  require_msg (check_result (equal toklist)) prtoks testf s
end

fun failtest (s, substring) =
    let
      fun pr s = "Testing failing lex of " ^ Lib.quote (String.toString s)
      fun check substring (LEX_ERR(s, _)) =
            String.isSubstring substring s
        | check _ _ = false
    in
      shouldfail {testfn = testf, printresult = prtoks, printarg = pr,
                  checkexn = check substring}
                 s
    end

val ai = Arbnum.fromInt
fun snum i = Numeral(ai i, NONE)
fun stdstr s = StrLit{ldelim = "\"", contents = s}
fun charstr s = StrLit{ldelim = "#\"", contents = s}
fun guillstr s = StrLit{ldelim = "«", contents = s}
fun sguillstr s = StrLit{ldelim = "‹", contents = s}
in
val _ = app (ignore o test) [
      ("abc", [Ident "abc"]),
      ("’", [Ident "\226\128\153"]),
      ("\"\\172\"", [stdstr "\172"]),
      ("#\"c\"", [charstr "c"]),
      ("f#\"c\"", [Ident "f", charstr "c"]),
      ("f(#\"c\"", [Ident "f", Ident "(", charstr "c"]),
      ("(\"ab\\172\"++z)",
       [Ident "(", stdstr "ab\172", Ident "++", Ident "z", Ident ")"]),
      ("f\"ab\\172x\"++", [Ident "f", stdstr "ab\172x", Ident "++"]),
      ("+\"ab\\172\"++", [Ident "+", stdstr "ab\172", Ident "++"]),
      ("$+\"ab\\172\"++", [Ident "$+", stdstr "ab\172", Ident "++"]),
      ("12", [snum 12]),
      ("-12", [Ident "-", snum 12]),
      ("((-12", [Ident "(", Ident "(", Ident "-", snum 12]),
      ("0a", [Numeral(ai 0, SOME #"a")]),
      ("0", [snum 0]),
      ("(0xF", [Ident "(", snum 15]),
      ("01", [snum 1]),
      ("1.2", [Fraction{wholepart = ai 1, fracpart = ai 2, places = 1}]),
      ("-1.2", [Ident "-",
                Fraction{wholepart = ai 1, fracpart = ai 2, places = 1}]),
      ("~1.2", [Ident "~",
                Fraction{wholepart = ai 1, fracpart = ai 2, places = 1}]),
      ("(2n*e", [Ident "(", Numeral (ai 2, SOME #"n"), Ident "*", Ident "e"]),
      ("2_001", [snum 2001]),
      ("2.000_023", [Fraction{wholepart = ai 2, places = 6, fracpart = ai 23}]),
      ("(", [Ident "("]),
      (".", [Ident "."]),
      ("0.", [snum 0, Ident "."]),
      ("a0.", [Ident "a0", Ident "."]),
      ("-0.", [Ident "-", snum 0, Ident "."]),
      ("{2.3",
       [Ident "{", Fraction{wholepart = ai 2, places = 1, fracpart = ai 3}]),
      ("(a+1", [Ident "(", Ident"a", Ident"+", snum 1]),
      ("a--b->c", [Ident "a", Ident"--b->", Ident"c"]),
      ("(+)", [Ident "(", Ident "+", Ident ")"]),
      ("$ $$ $$$ $+ $if $a",
       [Ident "$", Ident "$$", Ident "$$$", Ident "$+", Ident "$if",
        Ident "$a"]),
      ("thy$id", [QIdent("thy", "id")]),
      ("(thy$id", [Ident "(", QIdent("thy", "id")]),
      ("(thy$id +", [Ident "(", QIdent("thy", "id"), Ident "+"]),
      ("(thy$id+", [Ident "(", QIdent("thy", "id"), Ident "+"]),
      ("+thy$id", [Ident "+", QIdent("thy", "id")]),
      ("thy$0", [QIdent("thy", "0")]),
      ("(thy$id\"foo\"", [Ident "(", QIdent ("thy", "id"), stdstr "foo"]),
      ("(thy$id#\"f\"", [Ident "(", QIdent ("thy", "id"), charstr "f"]),
      ("(thy$id«foo b»", [Ident "(", QIdent ("thy", "id"), guillstr "foo b"]),
      ("x+« f»", [Ident "x", Ident "+", guillstr " f"]),
      ("(thy$id‹foo b›", [Ident "(", QIdent ("thy", "id"), sguillstr "foo b"]),
      ("x+‹ f›", [Ident "x", Ident "+", sguillstr " f"]),
      ("foo$bar<foo$baz", [QIdent ("foo", "bar"), Ident "<",
                           QIdent ("foo", "baz")]),
      ("(bool$/\\", [Ident "(", QIdent ("bool", "/\\")]),
      ("*foo$bar<foo$baz", [Ident "*", QIdent ("foo", "bar"), Ident "<",
                            QIdent ("foo", "baz")]),
      ("nm_sub$id", [QIdent ("nm_sub", "id")]),
      ("+nm$id\"bar\"", [Ident "+", QIdent ("nm", "id"), stdstr "bar"]),
      ("+nm$id\"\"", [Ident "+", QIdent ("nm", "id"), stdstr ""]),
      ("nm$**", [QIdent("nm", "**")]),
      ("$+a", [Ident "$+", Ident "a"]),
      ("$==>", [Ident "$==>"]),
      ("bool$~", [QIdent("bool", "~")]),
      ("$~", [Ident "$~"]),
      ("$¬", [Ident "$¬"]),
      ("(<a+b>)", [Ident "(<", Ident "a", Ident "+", Ident "b", Ident ">)"]),
      ("f(<a+b>)", [Ident "f", Ident "(<", Ident "a", Ident "+", Ident "b",
                    Ident ">)"]),
      ("+(<a+b>)", [Ident "+", Ident "(<", Ident "a", Ident "+", Ident "b",
                    Ident ">)"]),
      ("((<a+b>)", [Ident "(", Ident "(<", Ident "a", Ident "+", Ident "b",
                    Ident ">)"]),
      ("::_", [Ident "::", Ident "_"]),             (* case pattern with CONS *)
      ("=\"\"", [Ident "=", stdstr ""]),                (* e.g., stringScript *)
      ("$-->", [Ident "$-->"]),                       (* e.g., quotientScript *)
      ("$var$(ab)", [Ident "ab"]),
      ("$var$(ab\\nc)", [Ident "ab\nc"]),
      ("$var$(ab\\nc\\))", [Ident "ab\nc)"]),
      ("$var$(% foo )", [Ident "% foo "]),
      ("$var$(% foo* )", [Ident "% foo* "]),
      ("$var$(% foo*\\z)", [Ident "% foo*"]),
      ("$var$(((foo)", [Ident "((foo"]),
      ("$var$(foo\"bar)", [Ident "foo\"bar"]),
      ("$var$(foo\\172bar)", [Ident "foo\172bar"]),
      ("($var$(foo\"bar)", [Ident "(", Ident "foo\"bar"]),
      ("$$var$(foo\"bar)", [Ident "$foo\"bar"]),
      ("(')", [Ident "(", Ident "'", Ident ")"]),   (* e.g., finite_mapScript *)
      ("λx.x", [Ident "λ", Ident "x", Ident ".", Ident "x"]),
      ("x'0,y)", [Ident "x'0", Ident ",", Ident "y", Ident ")"]),
      ("x'0)", [Ident "x'0", Ident ")"]),
      ("(x'0)", [Ident "(", Ident "x'0", Ident ")"]),
      ("x'²,y)", [Ident "x'", Ident "²", Ident ",", Ident "y", Ident ")"]),
      ("x'", [Ident "x'"]),
      ("x''", [Ident "x''"]),
      ("x'3'", [Ident "x'''"]),
      ("xa'3'a'", [Ident "xa'3'a'"]),
      ("x'⁴'", [Ident "x''''"]),
      ("map:=λh.", [Ident "map", Ident ":=", Ident "λ", Ident "h", Ident "."]),
      ("map:=\\h.", [Ident "map", Ident ":=\\", Ident "h", Ident "."])
    ]
val _ = List.app (ignore o failtest) [
      ("thy$$$", "qualified ident"),
      ("$var$(ab\n c)", "quoted variable"),
      ("'a", "can't begin with prime"),
      ("thy$1", "qualified ident")
]
end (* local - tests of term lexer *)

(* tests of type lexer *)
val _ = let
  open type_tokens
  fun prtoklist ts =
      "[" ^ String.concatWith ", " (map (token_string (fn _ => "_")) ts) ^ "]"
  fun test (s,toklist) =
      (tprint ("Type-lexing \"" ^ s ^ "\"");
       require_msg (check_result (equal toklist)) prtoklist lextest s)
in
  List.app (ignore o test) [
    ("bool", [TypeIdent "bool"]),
    ("min$bool", [QTypeIdent("min", "bool")]),
    ("α", [TypeVar "α"]),
    ("'a", [TypeVar "'a"]),
    ("bool->'a", [TypeIdent "bool", TypeSymbol "->", TypeVar "'a"]),
    ("min$bool1->min$bool2", [QTypeIdent("min", "bool1"), TypeSymbol "->",
                              QTypeIdent("min", "bool2")]),
    ("(α,bool)fun", [LParen, TypeVar "α", Comma, TypeIdent "bool", RParen,
                     TypeIdent "fun"]),
    ("(foo$ty2,foo$ty2) ty1",
     [LParen, QTypeIdent("foo", "ty2"), Comma, QTypeIdent("foo", "ty2"),
      RParen, TypeIdent"ty1"])
  ]
end (* let - tests of type lexer *)

val g0 = term_grammar.stdhol;
fun mTOK s = term_grammar_dtype.RE (HOLgrammars.TOK s)
val mTM = term_grammar_dtype.RE HOLgrammars.TM

local
  open term_grammar term_grammar_dtype
in
val cond_g =
    add_rule {
        term_name   = "COND",
        fixity      = Prefix 70,
        pp_elements = [PPBlock([mTOK "if", BreakSpace(1,2), mTM,
                                BreakSpace(1,0),
                                mTOK "then"], (CONSISTENT, 0)),
                       BreakSpace(1,2), mTM, BreakSpace(1,0),
                       mTOK "else", BreakSpace(1,2)],
        paren_style = OnlyIfNecessary,
        block_style = (AroundEachPhrase, (CONSISTENT, 0))} g0
val let_g =
    add_rule { pp_elements = [mTOK "let",
                              ListForm {
                                 separator = [mTOK ";"],
                                 cons = GrammarSpecials.letcons_special,
                                 nilstr = GrammarSpecials.letnil_special,
                                 block_info = (INCONSISTENT, 0)},
                              mTOK "in"],
               term_name = GrammarSpecials.let_special,
               paren_style = OnlyIfNecessary, fixity = Prefix 8,
               block_style = (AroundEachPhrase, (CONSISTENT, 0))} g0
val lf_g = add_listform g0
            { block_info = (CONSISTENT, 0),
              separator = [mTOK ";", BreakSpace(1,0)],
              leftdelim = [mTOK "["],
              rightdelim= [mTOK "]"],
              nilstr = "NIL", cons = "CONS"}
end;
fun isabsynlist slist a =
  let
    open Absyn
  in
    case slist of
        [] => (case a of IDENT (_, "NIL") => true | _ => false)
      | s1 :: rest =>
        (case a of
             APP(_, APP (_, IDENT(_, "CONS"), IDENT (_, el1)), a_rest) =>
               el1 = s1 andalso isabsynlist rest a_rest
           | _ => false)
  end
val _ = PP.prettyPrint
          (print, 75)
          (Parse.mlower
             (term_grammar.prettyprint_grammar
                (fn g =>fn _ => smpp.add_string "<term>")
                lf_g))

fun parsetest sl =
  let
    val s = "["^String.concatWith ";" sl^"]"
    val _ = tprint ("Parsing "^s)
    val a = TermParse.absyn lf_g type_grammar.min_grammar [QUOTE s]
  in
    if isabsynlist sl a then OK() else die "FAILED!"
  end

val _ = parsetest []
val _ = parsetest (map str (explode "ab"))
val _ = parsetest (map str (explode "abcdef"))

fun find_named_rule nm g =
  let
    open term_grammar_dtype term_grammar
  in
    List.map
      (fn PREFIX (STD_prefix rrs) =>
          List.filter (fn rr => #term_name rr = nm) rrs
      | _ => [])
      (grammar_rules g) |> List.concat
  end;

val _ = tprint "term_grammar.grammar_tokens (LET)"
val _ =
    let val result = term_grammar.grammar_tokens let_g
    in
      if Lib.set_eq result
                    ["\\", "|>", "<|", ")", "(", ".", ":", "updated_by",
                     ":=", "with", "let", "in", ";", "$"]
      then OK()
      else die ("\nFAILED ["^
                String.concatWith "," (map (fn s => "\""^s^"\"") result) ^ "]")
    end;

val _ = tprint "term_grammar.rule_elements (COND)"
val cond_rule = hd (find_named_rule "COND" cond_g)
val cond_rels = term_grammar.rule_elements (#elements cond_rule)
val _ = let
  open HOLgrammars
in
  if cond_rels = [TOK "if", TM, TOK "then", TM, TOK "else"] then OK()
  else die "FAILED"
end;

val _ = tprint "PrecAnalysis.rule_equalities (COND)"
val cond_eqns = PrecAnalysis.rule_equalities cond_rule
val _ = if Lib.set_eq cond_eqns [("if", true, "then"), ("then", true, "else")]
        then OK()
        else die "FAILED";

val _ = tprint "term_grammar.rule_elements (LET)"
val let_rule = hd (find_named_rule GrammarSpecials.let_special let_g)
val let_rels = term_grammar.rule_elements (#elements let_rule)
val _ = let
  open HOLgrammars GrammarSpecials
in
  if let_rels =
     [TOK"let", ListTM{nilstr=letnil_special, cons=letcons_special, sep=";"},
      TOK "in"]
  then OK ()
  else die "FAILED"
end;

fun prlist eqns =
  "[" ^ String.concatWith ", "
         (map (fn (s1,b,s2) => "(\"" ^ s1 ^ "\"," ^ Bool.toString b ^ ",\"" ^
                               s2 ^"\")")
              eqns) ^ "]";

val _ = tprint "PrecAnalysis.rule_equalities (LET)"
val let_eqns = PrecAnalysis.rule_equalities let_rule
val _ = if Lib.set_eq let_eqns
                      [("let", true, ";"), (";", true, ";"), (";", true, "in"),
                       ("let", false, "in"), ("let", true, "in"),
                       (";", false, "in")]
        then OK()
        else die ("FAILED\n  got: "^prlist let_eqns);

val _ = tprint "term_grammar.rules_for (LET)"
val let_rules = term_grammar.rules_for let_g GrammarSpecials.let_special
val _ = if length let_rules = 1 then OK() else die "FAILED"

val lsp1 = {nilstr="lnil",cons="lcons",sep=";"}
val lsp2 = {nilstr="lnil2",cons="lcons2",sep=";;"}
fun check (s1,s2) =
  case (s1,s2) of
      ("let", "in") => SOME lsp1
    | ("in", "end") => SOME lsp2
    | _ => NONE

val f = PrecAnalysis.check_for_listreductions check

open term_grammar_dtype GrammarSpecials
val S = HOLPP.add_string
fun prmsp {nilstr,cons,sep} = "{" ^ nilstr ^ "," ^ cons ^ "," ^ sep ^ "}"
fun prlr (s1,s2,sp) = "(" ^ s1 ^ ", " ^ s2 ^ ", " ^ prmsp sp ^ ")"
fun prlist p l = "[" ^ String.concatWith ", " (map p l) ^ "]"
fun prlrs lrs = prlist prlr lrs
fun prrel (TOK s) = "TOK \""^s^"\""
  | prrel TM = "TM"
  | prrel _ = "<Unexpected rule-element>"
fun prlspi (lsp,i1,i2) =
    "(" ^ prmsp lsp ^ "," ^ Int.toString i1 ^ "," ^ Int.toString i2 ^ ")"
fun prrm_result (rels,lspis) =
    "(" ^ prlist prrel rels ^ ", " ^ prlist prlspi lspis ^ ")"
fun require_msg_eqk v pr f k x = require_msgk (check_result (equal v)) pr f k x
fun require_msg_eq v pr f x = require_msg_eqk v pr f (fn _ => ()) x
fun require_eq v f x = require (check_result (equal v)) f x
fun rmlistrels r i = PrecAnalysis.remove_listrels (Exn.release r) i

fun listredn_test (nm, input, input', expected1, testseq) =
    let
      val _ = tprint ("check_for_listreductions (" ^ nm ^ ")")
      fun kont result =
          (tprint ("remove_listrels (" ^ nm ^ ")");
           require_msg_eq (input', testseq) (S o prrm_result)
                          (rmlistrels result) input)
    in
      require_msg_eqk expected1 (S o prlrs) f kont input
    end
val bare_let = [TOK "let", TM, TOK "in", TM]
val suffix_let = [TM, TOK "let", TM, TOK "in"]

val _ = List.app listredn_test [
      ("1 element prefix", [TOK "let", TM, TOK "in", TM], bare_let,
       [("let", "in", lsp1)], [(lsp1, 0, 1)]),
      ("0 element prefix", [TOK "let", TOK "in", TM], bare_let,
       [("let", "in", lsp1)], [(lsp1, 0, 0)]),
      ("1 element + ; prefix", [TOK "let", TM, TOK ";", TOK "in", TM], bare_let,
       [("let", "in", lsp1)], [(lsp1, 0, 1)]),
      ("2 element prefix", [TOK "let", TM, TOK ";", TM, TOK "in", TM], bare_let,
       [("let", "in", lsp1)], [(lsp1, 0, 2)]),
      ("1 element suffix", [TM, TOK "let", TM, TOK "in"], suffix_let,
       [("let", "in", lsp1)], [(lsp1, 1, 1)]),
      ("2 element suffix", [TM, TOK "let", TM, TOK ";", TM, TOK "in"],
       suffix_let, [("let", "in", lsp1)], [(lsp1,1,2)]),
      ("2 element + ; suffix",
       [TM, TOK "let", TM, TOK ";", TM, TOK ";", TOK "in"],
       suffix_let, [("let", "in", lsp1)], [(lsp1,1,2)]),
      ("0 element suffix", [TM, TOK "let", TOK "in"], suffix_let,
       [("let", "in", lsp1)], [(lsp1, 1, 0)])
    ]

val mk_var = Term.mk_var
val mk_comb = Term.mk_comb
val bool = Type.bool
val alpha = Type.alpha
val CONS_t = mk_var("CONS", bool --> (bool --> bool))
val NIL_t = mk_var("NIL", bool)
fun mk_list00 elty n c tmlist =
  let
    fun recurse ts =
      case ts of
          [] => Term.inst [alpha |-> elty] n
        | x::xs => mk_comb(mk_comb(Term.inst [alpha |-> elty] c, x),
                           recurse xs)
  in
    recurse tmlist
  end

fun mk_list0 elty n c s =
  mk_list00 elty n c (map (fn c => mk_var(str c, elty)) (String.explode s))

val mk_list = mk_list0 bool NIL_t CONS_t;

fun tmprint g =
  PP.pp_to_string 70
      (fn t =>
          Parse.mlower
            (term_pp.pp_term g
                             type_grammar.min_grammar
                             PPBackEnd.raw_terminal
                             t))

fun tpp msg expected g t =
  let
    val _ = tprint msg
    val result = tmprint g t
  in
    if result = expected then OK()
    else die ("\nFAILED - got >" ^ result ^"<")
  end handle e => die ("EXN-FAILED: "^General.exnMessage e)

val _ = tpp "Printing empty list form (var)" "[]" lf_g NIL_t
val _ = tpp "Printing CONS-list form [x] (var)" "[x]" lf_g (mk_list "x")
val _ = tpp "Printing CONS-list form [x;y] (var)" "[x; y]" lf_g (mk_list "xy")

val cCONS_t =
    Term.prim_new_const {Thy = "min", Name = "CONS"} (bool --> (bool --> bool))
val cNIL_t = Term.prim_new_const {Thy = "min", Name = "NIL"} bool
val cmk_list = mk_list0 bool cNIL_t cCONS_t

val _ = tpp "Printing nil (const, no overload)" "min$NIL" lf_g cNIL_t

val lfco_g = lf_g |> term_grammar.fupdate_overload_info
                       (Overload.add_overloading ("NIL", cNIL_t))
                  |> term_grammar.fupdate_overload_info
                       (Overload.add_overloading ("CONS", cCONS_t));

val _ = tpp "Printing nil (const, overload)" "[]" lfco_g cNIL_t
val _ = tpp "Printing CONS-list [x] (const, overload)" "[x]"
            lfco_g (cmk_list "x")

(* listform, const, overload, nil overloaded again (as EMPTY is in pred_set) *)
val lfcono_g =
    lfco_g |> term_grammar.fupdate_overload_info
                 (Overload.add_overloading ("altNIL", cNIL_t))

val _ = tpp "Printing nil (const, double-overload)" "[x]" lfcono_g
            (cmk_list "x")

val cINS_t = Term.prim_new_const{Thy = "min", Name = "INS"}
                       (alpha --> (alpha --> bool) --> (alpha --> bool))
val cEMP_t = Term.prim_new_const{Thy = "min", Name = "EMP"} (alpha --> bool)
fun add_setlistform g =
  term_grammar.add_listform g {
      block_info = (CONSISTENT, 0),
      separator = [mTOK ";", BreakSpace(1,0)],
      leftdelim = [mTOK "{"],
      rightdelim= [mTOK "}"],
      nilstr = "EMP", cons = "INS"}
    |> term_grammar.fupdate_overload_info
         (Overload.add_overloading ("EMP", cEMP_t))
    |> term_grammar.fupdate_overload_info
         (Overload.add_overloading ("INS", cINS_t))

val lfcop_g = g0 |> add_setlistform


val pbmk_list = mk_list0 bool cEMP_t cINS_t
fun ptpp msg exp t = tpp msg exp lfcop_g t

val _ = ptpp "Printing INS-list {x} (const, overload, polymorphic inst)" "{x}"
             (pbmk_list "x")

val _ = ptpp "Printing INS-list {x;y} (const, overload, polymorphic inst)"
             "{x; y}"
             (pbmk_list "xy")

val fx = mk_comb(mk_var("f", alpha --> bool), mk_var("x", alpha))
val y = mk_var("y", bool)
val bINS = Term.inst[alpha |-> bool] cINS_t
val bEMP = Term.inst[alpha |-> bool] cEMP_t
val l = mk_comb(mk_comb(bINS, fx), mk_comb(mk_comb(bINS, y), bEMP))
val _ = ptpp "Printing INS-list {f x;y} (const, overload, polymorphic inst)"
             "{f x; y}"

val lfcopuo_g = (* as before + Unicode-ish overload on EMP *)
  lfcop_g
   |> term_grammar.fupdate_overload_info
       (Overload.add_overloading ("∅", cEMP_t))
val _ = tpp "Printing INS-list (Unicode EMP) {x;y}" "{x; y}"
            lfcopuo_g (pbmk_list "xy")



val add_infixINS =
  term_grammar.add_rule {
         block_style = (AroundEachPhrase, (INCONSISTENT, 0)),
         fixity = Parse.Infixr 490,
         term_name = "INS",
         pp_elements = [HardSpace 1, mTOK "INSERT", BreakSpace(1,0)],
         paren_style = OnlyIfNecessary}

val lf_infixfirst_cop = g0 |> add_infixINS |> add_setlistform
val lf_copinfix_g = (* list first + infix INS *)
  g0 |> add_setlistform |> add_infixINS
fun get_stamps g =
  let
    open term_grammar_dtype
    val rules = term_grammar.rules_for g "INS"
    fun stamp fxty =
      Option.map #1
                 (List.find (fn (_, GRULE {fixity,...}) => fixity = fxty
                               | _ => false)
                            rules)
  in
    {c = stamp Closefix, i = stamp (Infix(RIGHT, 490))}
  end
fun optionToString f NONE = "NONE"
  | optionToString f (SOME x) = "SOME("^f x^")"
fun recordic {i,c} = "i="^optionToString Int.toString i^"; "^
                     "c="^optionToString Int.toString c

val _ = tprint "infix INS first grule timestamps"
val ic as {c, i} = get_stamps lf_infixfirst_cop
val _ = case ic of
            {i = SOME i0, c = SOME c0} =>
              if i0 < c0 then OK()
              else die ("\n FAILED: "^recordic ic)
          | _ => die ("\n FAILED: "^recordic ic)

val _ = tprint "infix INS second grule timestamps"
val ic as {c, i} = get_stamps lf_copinfix_g
val _ = case ic of
            {i = SOME i0, c = SOME c0} =>
              if c0 < i0 then OK()
              else die ("\n FAILED: "^recordic ic)
          | _ => die ("\n FAILED: "^recordic ic)

val _ = tpp "Printing INS-list (w/infix INS first) {x}" "{x}"
            lf_infixfirst_cop (pbmk_list "x")


val _ = tpp "Printing INS-list (w/infix INS second) {x}" "x INSERT {}"
            lf_copinfix_g (pbmk_list "x")

val _ = tpp "Printing applied EMPTY: {} x" "{} x" lf_infixfirst_cop
            (mk_comb(cEMP_t, mk_var("x", alpha)))

val _ = tpp "Printing applied non-empty 1: {x} y" "{x} y" lf_infixfirst_cop
            (mk_comb(pbmk_list "x", mk_var("y", bool)))

val _ = tpp "Printing applied non-empty 2: {x; y} z" "{x; y} z"
            lf_infixfirst_cop
            (mk_comb(pbmk_list "xy", mk_var("z", bool)))

open ParseDatatype
val _ = tprint
val ASTL_toString =
    ParseDatatype_dtype.list_toString ParseDatatype_dtype.toString
val mintyg = type_grammar.min_grammar
val vbool = dTyop{Tyop = "bool", Thy = SOME "min", Args = []}
fun pdparse s = parse mintyg [QUOTE s]
fun hdparse s = hparse mintyg [QUOTE s]

fun pdtest0 (nm, s,expected) =
  let
    val _ = tprint (nm ^ ": " ^ s)
    val res = (if nm = "p" then pdparse else hdparse) s
  in
    if res = expected then OK()
    else die ("FAILED:\n  "^ASTL_toString res)
  end
infix -=>
fun nm2parse nm = if nm = "p" then pdparse else hdparse
fun pdtest (nm, s, expected) =
  let
    val _ = tprint (nm ^ ": " ^ s)
  in
    timed (nm2parse nm)
          (exncheck (fn r => if r = expected then OK()
                             else die ("FAILED:\n  "^ASTL_toString r)))
          s
  end
fun pdfail (nm, s) =
  shouldfail {printarg = (fn s => nm ^ ": " ^ s ^ " (should fail)"),
              printresult = ASTL_toString,
              testfn = nm2parse nm,
              checkexn = is_struct_HOL_ERR "ParseDatatype"} s

fun vty1 -=> vty2 = dTyop{Tyop = "fun", Thy = SOME "min", Args = [vty1,vty2]}
fun recop s = dTyop{Thy = NONE, Tyop = s, Args = []}
val expected1 = [("ty", Constructors [("Cons", [vbool])])]
val expected2 = [("ty", Constructors [("Cons1", [vbool]),
                                      ("Cons2", [vbool, vbool -=> vbool])])]
val expected3 = [("ty", Record [("fld1", vbool), ("fld2", vbool -=> vbool)])]
fun listnm nm =
  [(nm, Constructors[("N", []), ("C",[dVartype "'a", recop "ty"])])]
val expected4 = listnm "ty"
val expected5 = [("C", Constructors[("foo", []), ("bar",[])])]
val expected6 = [("C", Constructors[("foo", [vbool, vbool])]),
                 ("D", Constructors[("bar", [vbool]), ("baz", [])])]
val _ = List.app pdtest [
  ("p", "ty = Cons of bool;", expected1),
  ("h", "ty = Cons bool;", expected1),
  ("h", "ty = Cons1 bool | Cons2 bool (bool -> bool);", expected2),
  ("h", "ty = Cons1 bool | Cons2 bool (bool->bool);", expected2),
  ("p", "ty = Cons1 of bool | Cons2 of bool => bool -> bool;", expected2),
  ("h", "ty = <| fld1 : bool ; fld2 : bool -> bool |>;", expected3),
  ("h", "ty = <| fld1 : bool ; fld2 : bool -> bool; |>;", expected3),
  ("h", "ty= <|fld1:bool;fld2:bool->bool; |>;", expected3),
  ("h", "ty = N | C 'a ty;", expected4),
  ("p", "ty = N | C of 'a => ty", expected4),
  ("h", "ty=N|C 'a ty;", expected4),
  ("h", "ty=N|C 'a ty", expected4),
  ("h", "ty= <|fld1:bool;fld2:bool->bool; |>;ty2=N|C 'a ty",
   expected3 @ listnm "ty2"),
  ("h", "C = | foo | bar", expected5),
  ("h", "C = foo bool bool; D = bar bool|baz", expected6)
]

val _ = List.app (ignore o pdfail) [("h", "C = foo bool->bool")]


(* string find-replace *)
local
val theta = map (fn (a,b) => {redex = a, residue = b})
                [("a", "xxx"), ("b", "zzzz"), ("abc", "y"), ("c", ""),
                 ("ca", "uu"), ("cb", "vv")]
val f = stringfindreplace.subst theta
fun test (inp,out) =
  let
    val _ = tprint ("String find/replace "^inp^" = "^out)
    val res = f inp
  in
    if res = out then OK()
    else die ("FAILED - Got "^res)
  end
in
val _ = List.app test [("abcd", "yd"), ("ab", "xxxzzzz"), ("c", ""),
                       ("cab", "uuzzzz"), ("", ""), ("xyz", "xyz"),
                       ("ccb", "vv")]
end (* local *)

val _ = tprint "rules_for finds record rule"
val G0 = term_grammar.stdhol
val recrules = term_grammar.rules_for G0 GrammarSpecials.reccons_special
val _ =
    let
      open term_grammar
    in
      case recrules of
          [(_, GRULE {pp_elements = RE (TOK "<|") :: _,...})] => OK()
        | _ => die "Couldn't find it"
    end

val _ = tprint "remove_termtok \"<|\" removes record rule"
val G' =
    term_grammar.remove_form_with_tok G0 {
      term_name = GrammarSpecials.recd_lform_name, tok = "<|"
    }
val _ =
    let
      open term_grammar
    in
      case term_grammar.rules_for G' GrammarSpecials.reccons_special of
          [] => OK()
        | _ => die "Nope - something still there!"
    end

local
  val pr = PP.pp_to_string 77 type_grammar.prettyprint_grammar
  fun testvs(testname, fname, g) =
    let
      val expected0 = let
        val istrm = TextIO.openIn fname
      in
        TextIO.inputAll istrm before TextIO.closeIn istrm
      end
      val expected = if String.sub(expected0, size expected0 - 1) = #"\n" then
                       String.extract(expected0, 0, SOME (size expected0 - 1))
                     else expected0
      val res = delete_trailing_wspace (pr g)
    in
      tprint testname;
      if res = expected then OK() else die ("\nFAILED!\n" ^ res)
    end
  open type_grammar
in
  val _ = app testvs [
        ("Testing ty-grammar p/printing (min_grammar)", "tygrammar.txt",
         min_grammar),
        ("Testing ty-grammar p/printing (min_grammar with non-printing abbrev)",
         "noprint_tygrammar.txt",
         min_grammar |> new_abbreviation {knm = {Name = "set", Thy = "scratch"},
                                          ty = alpha --> bool, print = true}
                     |> disable_abbrev_printing "set")
      ]
end (* tygrammar p/printing local *)

local
  open term_tokens
  fun test (s, expected) =
    let
      val _ = tprint ("Non-aggregating lex-test on "^s)
      fun check (Exn.Res (SOME (r, _))) =
            (case r of Ident s' => s' = expected | _ => false)
        | check _ = false
      fun pr NONE = "NONE"
        | pr (SOME (t, _)) = "SOME(" ^ token_string t ^ ")"
    in
      require_msg check pr (lex []) (qbuf.new_buffer [QUOTE s])
    end
in
val _ = List.app (ignore o test) [
      ("aa(", "aa"), ("((a", "("), ("¬¬", "¬"), ("¬¬p", "¬")
    ]
end (* local open term_tokens *)

val _ = let
  open term_grammar Absyn Portable
  val rTOK = RE o TOK
  datatype sexp = id of string | app of string * sexp list
  fun toString (id s) = s
    | toString (app(f,xs)) =
      "(" ^ f ^
      (case xs of [] => ""
                | _ => " " ^ String.concatWith " " (map toString xs)) ^ ")"
  fun dropA A a =
      case a of
          APP (_, a1, a2) => dropA (dropA [] a2::A) a1
        | IDENT (_, s) => (case A of [] => id s | _ => app(s, A))
        | _ => raise Fail "Unexpected Absyn form"
  val G = min_grammar
            |> add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                         fixity = Suffix 2100,
                         paren_style = OnlyIfNecessary,
                         pp_elements = [
                           rTOK "{",
                           ListForm {
                             separator = [rTOK ";", BreakSpace(1,0)],
                             block_info = (PP.CONSISTENT, 1),
                             cons = "icons",
                             nilstr = "inil"
                           },
                           rTOK "}"],
                         term_name = "top"}
  val testfn =
      toString o dropA [] o TermParse.absyn G type_grammar.min_grammar o
      single o QUOTE
  fun test (s,expected) =
      (tprint ("listspec-suffix: " ^ s);
       require_msg_eq expected HOLPP.add_string testfn s)
in
  List.app (ignore o test) [
    ("x {y}", "(top x (icons y inil))"),
    ("x {y;z;}", "(top x (icons y (icons z inil)))"),
    ("x {}", "(top x inil)")
  ]
end;

(* DBSearchParser tests *)
local val dbsptests = [
        ("", "", true),
        ("", "ab", true),
        ("ab", "", false),
        ("a*", "", true),
        ("abc", "ffgabchh", true),
        ("abc", "ffgabhch", false),
        ("left~or", "xor_exists_left_thm", true),
        ("(left~or)_", "xor_exists_left_thm", true),
        ("left|or", "exists_left_thm_or", true),
        ("ab(ab)*", "abababc", true),
        ("abab*", "aba", true),
        ("ab(ab)?", "aba", true),
        ("abab*", "ababb", true),
        ("ababb*", "abab", true),
        ("ababb*", "aba", false),
        ("ab~cd~ef", "efabxcd", true)
]

fun test(p,s,r) =
  (tprint (Lib.quote (String.toString p) ^ "  w/in  " ^
           Lib.quote (String.toString s) ^ " = " ^ Bool.toString r);
   require_msg (check_result (equal r))
               Bool.toString
               (fn (p,s) => DBSearchParser.contains_regexp p s)
               (p,s))
in
  val _ = List.app (with_flag(Feedback.emit_WARNING, false) test) dbsptests
end

val _ = exit_count0 failcount
