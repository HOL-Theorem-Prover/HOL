(*---------------------------------------------------------------------------
                Parsing datatype specifications

   The grammar we're parsing is:

       G ::=              id "=" <form>
       form ::=           <phrase> ( "|" <phrase> ) *  |  <record_defn>
       phrase ::=         id  | id "of" <under_constr>
       under_constr ::=   <ptype> ( "=>" <ptype> ) * | <record_defn>
       record_defn ::=    "<|"  <idtype_pairs> "|>"
       idtype_pairs ::=   id ":" <type> | id : <type> ";" <idtype_pairs>
       ptype ::=          <type> | "(" <type> ")"

  It had better be the case that => is not a type infix.  This is true of
  the standard HOL distribution.  In the event that => is an infix, this
  code will still work as long as the input puts the types in parentheses.
 ---------------------------------------------------------------------------*)

structure ParseDatatype :> ParseDatatype =
struct

 type tyname   = string

val ERR = Feedback.mk_HOL_ERR "ParseDatatype";
val ERRloc = Feedback.mk_HOL_ERRloc "ParseDatatype";

    open Abbrev
datatype pretype
   = dVartype of string
   | dTyop of {Tyop : string, Thy : string option, Args : pretype list}
   | dAQ of Type.hol_type

type field = string * pretype
type constructor = string * pretype list

datatype datatypeForm
   = Constructors of constructor list
   | Record of field list

type AST = tyname * datatypeForm

fun pretypeToType pty =
  case pty of
    dVartype s => Type.mk_vartype s
  | dTyop {Tyop = s, Thy, Args} => let
    in
      case Thy of
        NONE => Type.mk_type(s, map pretypeToType Args)
      | SOME t => Type.mk_thy_type{Tyop = s, Thy = t,
                                   Args = map pretypeToType Args}
    end
  | dAQ pty => pty

val bads = CharSet.addString(CharSet.empty, "()\"")

fun ident_munge dollared qb s locn = let
  val s0 = String.sub(s, 0)
in
  if Char.isAlpha s0 then
    if s <> "of" orelse dollared then (qbuf.advance qb; s)
    else raise ERRloc "ident" locn "Expected an identifier, got (reserved word) \"of\""
  else if s0 = #"$" then
    (* Allow leading dollar signs as quoting mechanism (for "of", but to
       also cope with potential user paranoia over names of infix
       constructors).
       Note that the base_lexer ensures that only one dollar sign is possible
       at the head of a BT_Ident string, and that it is followed by a
       non-empty string *)
    ident_munge true qb (String.extract(s, 1, NONE)) (locn.move_start 1 locn)
  else let
      val s_chars = CharSet.addString(CharSet.empty, s)
      val overlap = CharSet.intersect(bads, s_chars)
    in
      if CharSet.isEmpty overlap then (qbuf.advance qb; s)
      else raise ERRloc "ident" locn (s ^ " not a valid constructor/field/type name")
    end
end

fun ident qb =
    case qbuf.current qb of
      (base_tokens.BT_Ident s,locn) => ident_munge false qb s locn
    | (bt,locn) => raise ERRloc "ident" locn ("Expected an identifier, got "^
                                              base_tokens.toString bt)

fun pdtok_of qb = let
  open base_tokens CharSet
  fun advance () = qbuf.advance qb
in
  case qbuf.current qb of
    (t as BT_Ident s,locn) =>
    if Char.isAlpha (String.sub(s, 0)) then (advance, t, locn)
    else let
        (* use of CharSet bads here is really a check for just the parentheses
           as the other characters in bads shouldn't be occurring in
           symbolic identifiers *)
        val (ss1, ss2) = Substring.splitl (fn c => not (member(bads, c)))
                                          (Substring.all s)
        val s1 = Substring.string ss1
        val s2 = Substring.string ss2
      in
        if s1 = "" orelse s2 = "" then (advance, t, locn)
        else let val (locn',locn'') = locn.split_at (size s1) locn in
             ((fn () => qbuf.replace_current (BT_Ident s2,locn'') qb), BT_Ident s1, locn') end
      end
  | (t,locn) => (advance, t, locn)
end;


fun scan s qb = let
  val (adv, t, locn) = pdtok_of qb
in
  case t of
    base_tokens.BT_Ident s' => if s <> s' then
                                 raise ERRloc "scan" locn
                                           ("Wanted \""^s^"\"; got \""^s'^"\"")
                               else adv()
  | x => raise ERRloc "scan" locn ("Wanted \""^s^"\"; got \""^
                                   base_tokens.toString x^"\"")
end

fun qtyop {Tyop, Thy, Locn, Args} = dTyop {Tyop = Tyop, Thy = SOME Thy, Args = Args}
fun tyop ((s,locn), args) = dTyop {Tyop = s, Thy = NONE, Args = args}

fun parse_type strm =
  parse_type.parse_type {vartype = dVartype o #1, tyop = tyop, qtyop = qtyop,
                         antiq = dAQ} true
  (Parse.type_grammar()) strm

val parse_constructor_id = ident

fun parse_record_fld qb = let
  val fldname = ident qb
  val () = scan ":" qb
in
  (fldname, parse_type qb)
end

fun sepby1 sepsym p qb = let
  val i1 = p qb
  fun recurse acc =
      case Lib.total (scan sepsym) qb of
        NONE => List.rev acc
      | SOME () => recurse (p qb :: acc)
in
  recurse [i1]
end


fun parse_record_defn qb = let
  val () = scan "<|" qb
  val result = sepby1 ";" parse_record_fld qb
  val () = scan "|>" qb
in
  result
end

fun parse_phrase qb = let
  val constr_id = parse_constructor_id qb
in
  case qbuf.current qb of
    (base_tokens.BT_Ident "of",_) => let
      val _ = qbuf.advance qb
      val optargs = sepby1 "=>" parse_type qb
    in
      (constr_id, optargs)
    end
  | _ => (constr_id, [])
end

fun parse_form qb =
    case qbuf.current qb of
      (base_tokens.BT_Ident "<|",_) => Record (parse_record_defn qb)
    | _ => Constructors (sepby1 "|" parse_phrase qb)

fun parse_G qb = let
  val tyname = ident qb
  val () = scan "=" qb
in
  (tyname, parse_form qb)
end

fun fragtoString (QUOTE s) = s
  | fragtoString (ANTIQUOTE _) = " ^... "

fun quotetoString [] = ""
  | quotetoString (x::xs) = fragtoString x ^ quotetoString xs

fun parse q = let
  val strm = qbuf.new_buffer q
  val result = sepby1 ";" parse_G strm
in
  case qbuf.current strm of
    (base_tokens.BT_EOI,_) => result
  | (_,locn) => raise ERRloc "parse" locn
                             "Parse failed"
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
