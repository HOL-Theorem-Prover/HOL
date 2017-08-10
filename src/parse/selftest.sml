open PPBackEnd PP Lib Type testutils

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


fun test_terminal test_bg (terminal:t) =
let
   val pp_out = Portable.stdOut_ppstream ();
   val {add_string, add_xstring, add_newline, add_break,
        begin_style, end_style, begin_block, end_block, ...} =
       with_ppstream terminal pp_out
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
in
   PP.clear_ppstream pp_out;
   (#begin_block terminal) pp_out INCONSISTENT 0;

   add_string "Terminal testing"; add_newline();
   add_string "================"; add_newline();
   add_newline();

   add_string "Annotations:"; add_newline();
   add_string "------------"; add_newline();
   add_ann_string ("Bound variable", BV (bool, fn () => ": bool"));
   add_newline();
   add_ann_string ("Free variable", FV (bool, fn () => ": bool"));
   add_newline();
   add_ann_string ("Type variable", TyV);
   add_newline();
   add_ann_string ("TySyn", TySyn (fn () => "TySyn"));
   add_newline();
   add_ann_string ("TyOp", TyOp (fn () => "TyOp"));
   add_newline();
   add_ann_string ("Const", Const {Name = "test-name", Thy = "test-thy",
                                   Ty = (Type.bool, fn () => "bool")});
   add_newline();
   add_ann_string ("Note", Note "Some note") ;
   add_newline();

   add_newline(); add_newline();

   add_string "Basic styles:"; add_newline();
   add_string "-------------"; add_newline();
   add_string "default style"; add_newline();
   begin_style [Bold]; add_string "Bold"; end_style(); add_newline();
   begin_style [Underline]; add_string "Underline"; end_style(); add_newline();
   map (fn c => (
      add_string "Foreground ";
      begin_style [FG c];
          add_string (color_name_fw c);
      end_style(); add_newline())) color_list;
   map (fn c => (
      add_string "Background ";
      begin_style [BG c];
          add_string (color_name_fw c);
      end_style(); add_newline())) color_list;

   add_newline(); add_newline();

   if test_bg then (
      add_string "All style combinations:"; add_newline();
      add_string "------------------------"; add_newline()
   ) else (
      add_string "All style combinations (without background color):"; add_newline();
      add_string "--------------------------------------------------"; add_newline()
   );
   map (fn (s, styL) => (
      begin_style styL;
          add_string s;
      end_style(); add_newline())) full_styles;
   add_newline();add_newline();

   (#end_block terminal) pp_out;
   PP.flush_ppstream pp_out
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



(* -------------------------------------------------------------------------- *)
(* Test code for style errors (non terminated style)                          *)
(* -------------------------------------------------------------------------- *)

fun test_style_error (terminal:t) =
let
   val pp_out = Portable.stdOut_ppstream ();
   val {add_string, add_xstring, add_newline, add_break,
        begin_style, end_style, begin_block, end_block, ...} =
       with_ppstream terminal pp_out
in
   PP.clear_ppstream pp_out;
   (#begin_block terminal) pp_out INCONSISTENT 0;

   add_string "Style error";
   begin_style [Bold]; add_string "...."; add_newline();

   (#end_block terminal) pp_out;
   PP.flush_ppstream pp_out
end;


(* ----------------------------------------------------------------------
    Tests of the base lexer
   ---------------------------------------------------------------------- *)

val _ = print "** Testing basic lexing functionality\n\n"
open base_tokens

fun quoteToString [QUOTE s] = "`"^s^"`"
  | quoteToString _ = die "Bad test quotation"

fun test (q, slist) = let
  val _ = tprint ("Testing " ^ quoteToString q)
in
  if map (base_tokens.toString o #1) (qbuf.lex_to_toklist q) <> slist then
    die "FAILED!"
  else OK()
end handle LEX_ERR (s,_) => die ("FAILED!\n  [LEX_ERR "^s^"]")
         | e => die ("FAILED\n ["^exnMessage e^"]")

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
                  (`"(*"`, ["\"(*\""])
                 ]

(* tests of the term lexer *)
fun test (s, toklist : unit term_tokens.term_token list) = let
  val _ = tprint ("Term token testing " ^ Lib.quote s)
in
  if term_tokens.lextest [] s = toklist then OK()
  else die "FAILED!"
end handle LEX_ERR (s,_) => die ("FAILED!\n  [LEX_ERR "^s^"]")
         | e => die ("FAILED\n ["^exnMessage e^"]")

open term_tokens
val ai = Arbnum.fromInt
val _ = app test [("abc", [Ident "abc"]),
                  ("12", [Numeral (ai 12, NONE)]),
                  ("-12", [Ident "-", Numeral (ai 12, NONE)]),
                  ("((-12", [Ident "(", Ident "(", Ident "-",
                             Numeral (ai 12, NONE)]),
                  ("1.2", [Fraction{wholepart = ai 1, fracpart = ai 2,
                                    places = 1}]),
                  ("-1.2", [Ident "-",
                            Fraction{wholepart = ai 1, fracpart = ai 2,
                                     places = 1}]),
                  ("~1.2", [Ident "~",
                            Fraction{wholepart = ai 1, fracpart = ai 2,
                                     places = 1}]),
                  ("(2n*e", [Ident "(", Numeral (ai 2, SOME #"n"),
                             Ident "*", Ident "e"]),
                  ("2_001", [Numeral (ai 2001, NONE)]),
                  ("2.000_023", [Fraction{wholepart = ai 2, places = 6,
                                          fracpart = ai 23}]),
                  ("0.", [Numeral (ai 0, NONE), Ident "."]),
                  ("a0.", [Ident "a0", Ident "."]),
                  ("-0.", [Ident "-", Numeral (ai 0, NONE), Ident "."]),
                  ("{2.3", [Ident "{", Fraction{wholepart = ai 2, places = 1,
                                                fracpart = ai 3}])
                  ]

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
end;

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

fun check (s1,s2) =
  case (s1,s2) of
      ("let", "in") => SOME 1
    | ("in", "end") => SOME 2
    | _ => NONE

val f = PrecAnalysis.check_for_listreductions check

val _ = tprint "PrecAnalysis.check_for_listreductions 1"
val result = let open term_grammar_dtype in
               f [TOK "let", TM, TOK "in", TM]
             end
val _ = if result = [("let", "in", 1)] then OK() else die "FAILED";

val _ = tprint "PrecAnalysis.check_for_listreductions 2"
val result = let open term_grammar_dtype in
               f [TOK "let", TM, TOK ";", TOK "in", TM]
             end
val _ = if result = [("let", "in", 1)] then OK() else die "FAILED";

val _ = tprint "PrecAnalysis.check_for_listreductions 3"
val result = let open term_grammar_dtype in
               f [TOK "let", TM, TOK ";", TM, TOK "in", TM]
             end
val _ = if result = [("let", "in", 1)] then OK() else die "FAILED";

(*

full test including backgrounds
val _ = test_terminal true (!Parse.current_backend)


error testing for backends (be careful)
val _ = test_style_error (!Parse.current_backend)

*)
