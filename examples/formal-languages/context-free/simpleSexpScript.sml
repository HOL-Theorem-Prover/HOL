open HolKernel Parse boolLib bossLib;

local open stringLib in end

open grammarLib
open monadsyntax lcsymtacs pegTheory

val _ = new_theory "simpleSexp";

val _ = overload_on ("monad_bind", ``OPTION_BIND``)
val _ = overload_on ("monad_unitbind", ``OPTION_IGNORE_BIND``)
val _ = temp_overload_on ("return", ``SOME``)
val _ = temp_overload_on ("SOME", ``SOME``)

val _ = computeLib.add_persistent_funs ["option.OPTION_BIND_def",
                                        "option.OPTION_IGNORE_BIND_def",
                                        "option.OPTION_GUARD_def",
                                        "option.OPTION_CHOICE_def"]

val _ = overload_on ("assert", ``option$OPTION_GUARD : bool -> unit option``)
val _ = overload_on ("++", ``option$OPTION_CHOICE``)


val _ = Datatype`
  sexp = SX_CONS sexp sexp
       | SX_SYM string
       | SX_NUM num
       | SX_STR string
`;

val _ = add_numeral_form(#"s", SOME "SX_NUM")
val _ = overload_on ("nil", ``SX_SYM "nil"``)
val _ = add_listform { block_info = (PP.INCONSISTENT, 0),
                       cons = "SX_CONS", leftdelim = [Parse.TOK "⦇"],
                       nilstr = "nil", rightdelim = [Parse.TOK "⦈"],
                       separator = [Parse.TOK ";", BreakSpace(1,0)]}

val _ = add_rule { block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0)),
                   fixity = Closefix,
                   paren_style = OnlyIfNecessary,
                   pp_elements = [Parse.TOK "⦇", TM, HardSpace 1,
                                  Parse.TOK "•", BreakSpace(1, 0), TM,
                                  Parse.TOK "⦈"],
                   term_name = "SX_CONS" }


val _ = overload_on ("’", ``λs. ⦇ SX_SYM "quote" ; s ⦈``)

val valid_first_symchar_def = Define`
  valid_first_symchar c ⇔ isGraph c ∧ c ∉ {#"'"; #"("; #")"; #"."; #"\""} ∧ ¬isDigit c`;

val valid_symchar_def =  Define`
  valid_symchar c ⇔ isGraph c ∧ c ∉ {#"'"; #"("; #")"}`;

val valid_symbol_def = Define`
   (valid_symbol "" ⇔ F) ∧
   (valid_symbol (c::cs) ⇔ valid_first_symchar c ∧ EVERY valid_symchar cs)`;

val valid_sexp_def = Define`
  (valid_sexp (SX_SYM s) ⇔ valid_symbol s) ∧
  (valid_sexp (SX_CONS s1 s2) ⇔ valid_sexp s1 ∧ valid_sexp s2) ∧
  (valid_sexp s ⇔ T)`;
val _ = export_rewrites["valid_first_symchar_def","valid_symchar_def","valid_symbol_def","valid_sexp_def"];

val destSXNUM_def = Define`
  destSXNUM (SX_NUM n) = n
`;

val destSXSYM_def = Define`
  destSXSYM (SX_SYM s) = s
`;

val destSXCONS_def = Define`
  destSXCONS (SX_CONS a d) = (a,d)
`;

val strip_sxcons_def = Define`
  strip_sxcons s =
    case s of
        SX_CONS h t => OPTION_MAP (CONS h) (strip_sxcons t)
      | SX_SYM s => if s = "nil" then SOME []
                    else NONE
      | _ => NONE
`;

val sxMEM_def = Define`
  sxMEM e s ⇔ ∃l. strip_sxcons s = SOME l ∧ MEM e l
`;

val sexp_size_def = definition"sexp_size_def";

val sxMEM_sizelt = store_thm(
  "sxMEM_sizelt",
  ``∀s1 s2. sxMEM s1 s2 ⇒ sexp_size s1 < sexp_size s2``,
  dsimp[sxMEM_def] >> Induct_on `s2` >>
  dsimp[Once strip_sxcons_def, sexp_size_def] >> rpt strip_tac >>
  res_tac >> simp[]);

val dstrip_sexp_def = Define`
  (dstrip_sexp (SX_CONS sym args) =
     case sym of
         SX_SYM s => OPTION_MAP (λt. (s, t)) (strip_sxcons args)
       | _ => NONE) ∧
  (dstrip_sexp _ = NONE)
`;

val tokmap = List.foldl (fn ((s,t), acc) => Binarymap.insert(acc, s, t))
                        (Binarymap.mkDict String.compare)
  [("(", ``#"("``), (")", ``#")"``), ("'", ``#"'"``),
   ("\"", ``#"\""``), ("\\", ``#"\\"``), (".", ``#"."``)]

fun toklookup s =
  Binarymap.find(tokmap, s)
  handle Binarymap.NotFound => raise Fail ("No tok def for "^s)

val ginfo = { tokmap = toklookup,
              tokty = ``:char``, nt_tyname = "sexpNT", start = "sexp",
              gname = "sexpG", mkntname = (fn s => "sxnt_" ^ s) }


val sexpG_def = mk_grammar_def ginfo `
  sexp ::= WSsexp grabWS ;
  WSsexp ::= grabWS sexp0 ;
  grabWS ::= WS grabWS | ;
  WS ::= ^(``{ c | isSpace c }``) ;
  sexp0 ::= sexpsym | sexpnum | sexpstr | "(" sexpseq grabWS ")"
         | "(" sexp "." sexp ")" | "'" WSsexp ;

  sexpseq ::= WSsexp sexpseq | ;

  sexpnum ::= sexpnum digit | digit ;
  digit ::= ^(``{ c | isDigit c}``);

  sexpstr ::= "\"" strcontents "\"" ;
  strcontents ::= | strchar strcontents ;
  strchar ::= normstrchar | escapedstrchar ;
  normstrchar ::= ^(``{ c | isPrint c ∧ c ≠ #"\\" ∧ c ≠ #"\"" }``) ;
  escapedstrchar ::= "\\" escapablechar ;
  escapablechar ::= "\\" | "\"" ;

  sexpsym ::= first_symchar symchars ;
  first_symchar ::= ^(``{ c | valid_first_symchar c }``)
 ;
  symchars ::= symchar symchars | ;
  symchar ::= ^(``{ c | valid_symchar c }``);
`;

val _ = type_abbrev("NT", ``:sexpNT inf``)
val _ = overload_on("mkNT", ``INL : sexpNT -> NT``)
val _ = overload_on ("TK", ``TOK : char -> (char,sexpNT)symbol``)


val ptree_digit_def = Define`
  (ptree_digit (Lf _) = NONE) ∧
  (ptree_digit (Nd ntm args) =
     if ntm ≠ mkNT sxnt_digit then NONE
     else
       case args of
           [Lf tksym] =>
             do
               c <- destTOK tksym ;
               return (ORD c - ORD #"0")
             od
         | _ => NONE)
`;

val ptree_sexpnum_def = Define`
  (ptree_sexpnum (Lf _) = NONE) ∧
  (ptree_sexpnum (Nd ntm args) =
     if ntm ≠ mkNT sxnt_sexpnum then NONE
     else
       case args of
           [d] => ptree_digit d
         | [sn; d] =>
             do
                dn <- ptree_digit d ;
                snn <- ptree_sexpnum sn ;
                return (10 * snn + dn)
             od
         | _ => NONE)
`;


val ptree_WS_def = Define`
  (ptree_WS (Lf _) = NONE) ∧
  (ptree_WS (Nd ntm args) =
   if ntm ≠ mkNT sxnt_WS then NONE
   else
     case args of
       [c] => return ()
     | _ => NONE)`;

val ptree_grabWS_def = Define`
  (ptree_grabWS (Lf _) = NONE) ∧
  (ptree_grabWS (Nd ntm args) =
   if ntm ≠ mkNT sxnt_grabWS then NONE
   else
     case args of
       [w; g] =>
         do
           ptree_WS w;
           ptree_grabWS g;
           return ()
         od
     | _ => NONE)`;

val ptree_normstrchar_def = Define`
  (ptree_normstrchar (Lf _) = NONE) ∧
  (ptree_normstrchar (Nd ntm args) =
   if ntm ≠ mkNT sxnt_normstrchar then NONE
   else
     case args of
       [Lf(TK c)] => return c
     | _ => NONE)`;

val ptree_escapablechar_def = Define`
  (ptree_escapablechar (Lf _) = NONE) ∧
  (ptree_escapablechar (Nd ntm args) =
   if ntm ≠ mkNT sxnt_escapablechar then NONE
   else
     case args of
       [Lf(TK c)] => return c
     | _ => NONE)`;

val ptree_escapedstrchar_def = Define`
  (ptree_escapedstrchar (Lf _) = NONE) ∧
  (ptree_escapedstrchar (Nd ntm args) =
   if ntm ≠ mkNT sxnt_escapedstrchar then NONE
   else
     case args of
       [b; c] =>
         if b = Lf(TK#"\\") then
           ptree_escapablechar c
         else NONE
     | _      => NONE)`;

val ptree_strchar_def = Define`
  (ptree_strchar (Lf _) = NONE) ∧
  (ptree_strchar (Nd ntm args) =
   if ntm ≠ mkNT sxnt_strchar then NONE
   else
     case args of
       [c] => ptree_normstrchar c ++ ptree_escapedstrchar c
     | _   => NONE)`;

val ptree_strcontents_def = Define`
  (ptree_strcontents (Lf _) = NONE) ∧
  (ptree_strcontents (Nd ntm args) =
   if ntm ≠ mkNT sxnt_strcontents then NONE
   else
     case args of
       [] => return ""
     | [sc; ss] =>
       do
         c <- ptree_strchar sc;
         s <- ptree_strcontents ss;
         return (c::s)
       od
     | _ => NONE)`;

val ptree_sexpstr_def = Define`
  (ptree_sexpstr (Lf _) = NONE) ∧
  (ptree_sexpstr (Nd ntm args) =
   if ntm ≠ mkNT sxnt_sexpstr then NONE
   else
     case args of
       [lq; s; rq] =>
       if (lq = Lf(TK#"\"") ∧ rq = Lf(TK#"\"")) then
         ptree_strcontents s
       else NONE
     | _ => NONE)`;

val ptree_first_symchar_def = Define`
  (ptree_first_symchar (Lf _) = NONE) ∧
  (ptree_first_symchar (Nd ntm args) =
   if ntm ≠ mkNT sxnt_first_symchar then NONE
   else
     case args of
       [Lf(TK c)] => return c
     | _ => NONE)`;

val ptree_symchar_def = Define`
  (ptree_symchar (Lf _) = NONE) ∧
  (ptree_symchar (Nd ntm args) =
   if ntm ≠ mkNT sxnt_symchar then NONE
   else
     case args of
       [Lf(TK c)] => return c
     | _ => NONE)`;

val ptree_symchars_def = Define`
  (ptree_symchars (Lf _) = NONE) ∧
  (ptree_symchars (Nd ntm args) =
   if ntm ≠ mkNT sxnt_symchars then NONE
   else
     case args of
       [f;s] =>
         do
           c <- ptree_symchar f;
           cs <- ptree_symchars s;
           return (c::cs)
         od
     | _ => NONE)`;

val ptree_sexpsym_def = Define`
  (ptree_sexpsym (Lf _) = NONE) ∧
  (ptree_sexpsym (Nd ntm args) =
   if ntm ≠ mkNT sxnt_sexpsym then NONE
   else
     case args of
       [f;s] =>
         do
           c <- ptree_first_symchar f;
           cs <- ptree_symchars s;
           return (c::cs)
         od
     | _ => NONE)`;

val ptree_sexp_def = Define`
  (ptree_sexp (Lf _) = NONE) ∧
  (ptree_sexp (Nd ntm args) =
   if ntm ≠ mkNT sxnt_sexp then NONE
   else
     case args of
         [w; g] => do ptree_grabWS g; ptree_WSsexp w od
     |   _      => NONE) ∧
  (ptree_WSsexp (Lf _) = NONE) ∧
  (ptree_WSsexp (Nd ntm args) =
   if ntm ≠ mkNT sxnt_WSsexp then NONE
   else
     case args of
       [g; s] => do ptree_grabWS g; ptree_sexp0 s od
     | _      => NONE) ∧
  (ptree_sexp0 (Lf _) = NONE) ∧
  (ptree_sexp0 (Nd ntm args) =
   if ntm ≠ mkNT sxnt_sexp0 then NONE
   else
     case args of
       [s] =>
         do x <- ptree_sexpsym s; return (SX_SYM x) od ++
         do x <- ptree_sexpnum s; return (SX_NUM x) od ++
         do x <- ptree_sexpstr s; return (SX_STR x) od
     | [q;w] =>
       if q = Lf (TK#"'") then ptree_WSsexp w else NONE
     | [lp; s; g; rp] =>
       if lp = Lf (TK#"(") ∧ rp = Lf (TK#")") then
         do
           ptree_grabWS g;
           ptree_sexpseq s
         od
       else NONE
     | [lp; sa; dot; sd; rp] =>
       if lp = Lf (TK#"(") ∧ dot = Lf (TK#".") ∧ rp = Lf (TK#")") then
         do
           a <- ptree_sexp sa;
           d <- ptree_sexp sd;
           return (SX_CONS a d)
         od
       else NONE
     | _ => NONE) ∧
  (ptree_sexpseq (Lf _) = NONE) ∧
  (ptree_sexpseq (Nd ntm args) =
   if ntm ≠ mkNT sxnt_sexpseq then NONE
   else
     case args of
       [] => return nil
     | [w; s] =>
         do
           x <- ptree_WSsexp w;
           r <- ptree_sexpseq s;
           return (SX_CONS x r)
         od
     | _ => NONE)`;


val _ = export_theory()
