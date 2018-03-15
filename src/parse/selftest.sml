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
  open OldPP
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
val lf_g = add_listform g0
            { block_info = (CONSISTENT, 0),
              separator = [mTOK ";", BreakSpace(1,0)],
              leftdelim = [mTOK "["],
              rightdelim= [mTOK "]"],
              nilstr = "NIL", cons = "CONS"}
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

val _ = tprint "term_grammar.grammar_tokens (LET)"
val _ =
    let val result = term_grammar.grammar_tokens let_g
    in
      if Lib.set_eq result
                    ["\\", "|>", "<|", ")", "(", ".", ":", "updated_by",
                     ":=", "with", "let", "in", ";"]
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
val _ = tprint "PrecAnalysis.check_for_listreductions 1"
val input = [TOK "let", TM, TOK "in", TM]
val result = f input
val _ = if result = [("let", "in", lsp1)] then OK() else die "FAILED";

val _ = tprint "PrecAnalysis.remove_listrels 1"
val remove_result = PrecAnalysis.remove_listrels result input
val _ = if remove_result = ([TOK "let", TM, TOK "in", TM], [(lsp1, [0])])
        then OK()
        else die "FAILED";

val _ = tprint "PrecAnalysis.check_for_listreductions 2"
val input = [TOK "let", TM, TOK ";", TOK "in", TM]
val result = f input
val _ = if result = [("let", "in", lsp1)] then OK() else die "FAILED";

val _ = tprint "PrecAnalysis.remove_listrels 2"
val remove_result = PrecAnalysis.remove_listrels result input
val _ = if remove_result = ([TOK "let", TM, TOK "in", TM], [(lsp1, [0])])
        then OK()
        else die "FAILED";

val _ = tprint "PrecAnalysis.check_for_listreductions 3"
val input = [TOK "let", TM, TOK ";", TM, TOK "in", TM]
val result = f input
val _ = if result = [("let", "in", lsp1)] then OK() else die "FAILED";

val _ = tprint "PrecAnalysis.remove_listrels 3"
val remove_result = PrecAnalysis.remove_listrels result input
val _ = if remove_result = ([TOK "let", TM, TOK "in", TM], [(lsp1, [0,1])])
        then OK()
        else die "FAILED";

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
      (term_pp.pp_term g type_grammar.min_grammar PPBackEnd.raw_terminal);

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

fun pdtest (nm, s,expected) =
  let
    val _ = tprint (nm ^ ": " ^ s)
    val res = (if nm = "p" then pdparse else hdparse) s
  in
    if res = expected then OK()
    else die ("FAILED:\n  "^ASTL_toString res)
  end
infix -=>

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
val _ = List.app pdtest [
  ("p", "ty = Cons of bool;", expected1),
  ("h", "ty = Cons bool;", expected1),
  ("h", "ty = Cons1 bool | Cons2 bool (bool -> bool);", expected2),
  ("h", "ty = <| fld1 : bool ; fld2 : bool -> bool |>;", expected3),
  ("h", "ty = <| fld1 : bool ; fld2 : bool -> bool; |>;", expected3),
  ("h", "ty= <|fld1:bool;fld2:bool->bool; |>;", expected3),
  ("h", "ty = N | C 'a ty;", expected4),
  ("p", "ty = N | C of 'a => ty", expected4),
  ("h", "ty=N|C 'a ty;", expected4),
  ("h", "ty=N|C 'a ty", expected4),
  ("h", "ty= <|fld1:bool;fld2:bool->bool; |>;ty2=N|C 'a ty",
   expected3 @ listnm "ty2"),
  ("h", "C = | foo | bar", expected5)
]


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

(*

full test including backgrounds
val _ = test_terminal true (!Parse.current_backend)


error testing for backends (be careful)
val _ = test_style_error (!Parse.current_backend)

*)
