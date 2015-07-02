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

val destSXNUM_def = Define`
  destSXNUM (SX_NUM n) = n
`;

val destSXSYM_def = Define`
  destSXSYM (SX_SYM s) = s
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
  first_symchar ::=
    ^(``{ c | isGraph c ∧ c ∉ {#"'"; #"("; #")"} ∧ ¬isDigit c}``) ;
  symchars ::= symchar symchars | ;
  symchar ::= ^(``{ c | isGraph c ∧ c ∉ {#"'"; #"("; #")"}}``);
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



val _ = export_theory()
