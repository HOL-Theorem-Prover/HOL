(*---------------------------------------------------------------------------
                Parsing datatype specifications
 ---------------------------------------------------------------------------*)

structure ParseDatatype :> ParseDatatype =
struct

fun ERR s1 s2 =
 Exception.HOL_ERR
  {origin_structure = "ParseDatatype",
   origin_function = s1,
   message = s2};

(* grammar we're parsing is:
    G ::=         id "=" <phrase> ( "|" <phrase> ) *
    phrase ::=    id  | id "of" <ptype> ( "=>" <ptype> ) *
    ptype ::=     <type> | "(" <type> ")"
 *
 * It had better be the case that => is not a type infix.  This is true of
 * the standard HOL distribution.  In the event that => is an infix, this
 * code will still work as long as the input puts the types in parentheses.
 *)

open optmonad
open monadic_parse
open fragstr
infix >> >- >-> ++

datatype pretype =
  dVartype of string | dTyop of (string * pretype list) |
  dAQ of Type.hol_type

fun parse_type strm =
  parse_type.parse_type {vartype = dVartype, tyop = dTyop, antiq = dAQ} true
  (Parse.type_grammar()) strm
fun parse_constructor_id s =
  (token (many1_charP (fn c => Lexis.in_class (Lexis.hol_symbols, Char.ord c)))
   ++
   token normal_alpha_ident) s

val parse_phrase =
  parse_constructor_id >-                            (fn constr_id =>
  optional (symbol "of" >>
            sepby1 (symbol "=>") parse_type) >-     (fn optlist =>
  case optlist of
    NONE => return (constr_id, [])
  | SOME tylist => return (constr_id, tylist)))

val parse_G =
  token normal_alpha_ident >-                        (fn tyname =>
  symbol "=" >> sepby1 (symbol "|") parse_phrase >-  (fn phrlist =>
  return (tyname, phrlist)))

type datatypeAST = string * ((string * pretype list) list)

fun fragtoString (QUOTE s) = s
  | fragtoString (ANTIQUOTE _) = " ^... "
fun quotetoString [] = ""
  | quotetoString (x::xs) = fragtoString x ^ quotetoString xs

fun parse strm = let
  val result = fragstr.parse (sepby1 (symbol ";") parse_G) strm
in
  case result of
    (strm, SOME result) => result
  | (strm, NONE) =>
      raise ERR "parse"
        ("Parse failed with input remaining: "^quotetoString strm)
end


(*---------------------------------------------------------------------------
          tests

quotation := true;

parse `foo = NIL | CONS of 'a => 'a foo`;
parse `list = NIL | :: of 'a => list`;
parse `void = Void`;
parse `pair = CONST of 'a#'b`;
parse `onetest = OOOO of one`;
parse `tri = Hi | Lo | Fl`;
parse `iso = ISO of 'a`;
parse `ty = C1 of 'a
          | C2
          | C3 of 'a => 'b => ty
          | C4 of ty => 'c => ty => 'a => 'b
          | C5 of ty => ty`;
parse `bintree = LEAF of 'a | TREE of bintree => bintree`;
parse `typ = C of one
                  => (one#one)
                  => (one -> one -> 'a list)
                  => ('a,one#one,'a list) ty`;
parse `Typ = D of one
                  # (one#one)
                  # (one -> one -> 'a list)
                  # ('a, one#one, 'a list) ty`;

parse `atexp = var_exp of var
           | let_exp of dec => exp ;

       exp = aexp    of atexp
           | app_exp of exp => atexp
           | fn_exp  of match ;

     match = match  of rule
           | matchl of rule => match ;

      rule = rule of pat => exp ;

       dec = val_dec   of valbind
           | local_dec of dec => dec
           | seq_dec   of dec => dec ;

   valbind = bind  of pat => exp
           | bindl of pat => exp => valbind
           | rec_bind of valbind ;

       pat = wild_pat
           | var_pat of var`;

val state = Type`:ind->bool`;
val nexp  = Type`:^state -> ind`;
val bexp  = Type`:^state -> bool`;

parse `comm = skip
            | :=    of bool list => ^nexp
            | ;;    of comm => comm
            | if    of ^bexp => comm => comm
            | while of ^bexp => comm`;

parse `ascii = ASCII of bool=>bool=>bool=>bool=>bool=>bool=>bool=>bool`;
*)


end;
