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

type prekind = Prekind.prekind
type prerank = Prerank.prerank

val ERR = Feedback.mk_HOL_ERR "ParseDatatype";
val ERRloc = Feedback.mk_HOL_ERRloc "ParseDatatype";

open Portable;

datatype pretype
   = dVartype of string * prekind * prerank
   | dContype of {Thy : string option, Tyop : string, Kind : prekind, Rank : prerank}
   | dTyApp  of pretype * pretype
   | dTyUniv of pretype * pretype
   | dTyAbst of pretype * pretype
   | dTyKindConstr of {Ty : pretype, Kind : prekind}
   | dTyRankConstr of {Ty : pretype, Rank : prerank}
 (*  | dTyop of {Tyop : string, Thy : string option, Args : pretype list} *)
   | dAQ of Type.hol_type

type field = string * pretype
type constructor = string * pretype list

datatype datatypeForm
   = Constructors of constructor list
   | Record of field list

type AST = string * datatypeForm

fun pretypeToType pty =
  case pty of
    dVartype (s,kd,rk) => Type.mk_vartype_opr (s, Prekind.toKind kd, Prerank.toRank rk)
  | dContype {Thy=SOME Thy,Tyop,Kind,Rank} => Type.mk_thy_con_type {Thy=Thy, Tyop=Tyop}
  | dContype {Thy=NONE,    Tyop,Kind,Rank} => Type.mk_con_type Tyop
  | dTyApp  (opr,arg)   => Type.mk_app_type(pretypeToType opr, pretypeToType arg)
  | dTyUniv (bvar,body) => Type.mk_univ_type(pretypeToType bvar, pretypeToType body)
  | dTyAbst (bvar,body) => Type.mk_abs_type (pretypeToType bvar, pretypeToType body)
  | dTyKindConstr {Ty,Kind} => pretypeToType Ty
  | dTyRankConstr {Ty,Rank} => pretypeToType Ty
(*
  | dTyop {Tyop = s, Thy, Args} => let
    in
      case Thy of
        NONE => Type.mk_type(s, map pretypeToType Args)
      | SOME t => Type.mk_thy_type{Tyop = s, Thy = t,
                                   Args = map pretypeToType Args}
    end
*)
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

fun tycon {Thy, Tyop, Kind, Rank} = dContype{Tyop=Tyop, Thy=Thy, Kind=Kind, Rank=Rank}

fun dTyop {Tyop, Thy, Args} =
  let fun mkprety acc [] = acc
        | mkprety acc (arg::args) = mkprety (dTyApp(acc,arg)) args
  in mkprety (dContype{Tyop=Tyop, Thy=Thy, Kind=Prekind.typ, Rank=Prerank.Zerorank}) Args
  end

fun dest_dTyop (dContype {Thy,Tyop,Kind,Rank}) = {Tyop=Tyop, Thy=Thy, Args=[]}
  | dest_dTyop (dTyApp(opr,arg)) = let val {Thy,Tyop,Args} = dest_dTyop opr
                                   in {Thy=Thy,Tyop=Tyop,Args=Args @ [arg]}
                                   end
  | dest_dTyop _ = raise ERR "dest_dTyop" "not a dTyop"

fun qtyop {Tyop, Thy, Locn, Args} = dTyop {Tyop = Tyop, Thy = SOME Thy, Args = Args}
fun tyop ((s,locn), args) = dTyop {Tyop = s, Thy = NONE, Args = args}

(* Building the kind parser: *)

val kd_antiq = type_pp.kd_antiq;
val dest_kd_antiq = type_pp.dest_kd_antiq;
val is_kd_antiq = type_pp.is_kd_antiq;

fun remove_kd_aq t =
  if is_kd_antiq t then dest_kd_antiq t
  else raise ERR "kind parser" "antiquotation is not of a kind"

fun kindcast {Ty,Kind,Locn} =
  dTyKindConstr {Ty=Ty,Kind=Kind}

fun rankcast {Ty,Rank,Locn} =
  dTyRankConstr {Ty=Ty,Rank=Rank}

fun mk_basevarkd(s,locn) = Prekind.PK(Prekind.Varkind s, locn)

fun kindop_to_qkindop ((kindop,locn), args) = let
  open Prekind
in
  if kindop = "ty" then PK(Typekind,locn)
  else if kindop = "=>" then PK(Arrowkind(hd args, hd(tl args)), locn)
  else raise ERR "kind parser" (kindop ^ " not a known kind operator")
end

fun do_qkindop {Thy:string, Kindop, Locn:locn.locn, Args} =
    kindop_to_qkindop ((Kindop,Locn), Args)

fun arity ((s, locn), n) = Prekind.mk_arity n

val kind_p1_rec = {varkind = mk_basevarkd, qkindop = do_qkindop,
                kindop = kindop_to_qkindop, arity = arity,
                antiq = fn x => Prekind.fromKind (remove_kd_aq x)}

val kindparser = parse_kind.parse_kind kind_p1_rec true (Parse.kind_grammar())

fun mk_conty{Thy,Tyop,Locn} =
       dContype{Thy=SOME Thy,Tyop=Tyop,Kind=Prekind.new_uvar(),Rank=Prerank.new_uvar()}

fun parse_type strm =
  parse_type.parse_type {vartype = dVartype o #1, tyop = tyop, qtyop = qtyop,
                         antiq = dAQ, kindcast = kindcast, rankcast = rankcast,
                         tycon = mk_conty, tyapp = dTyApp,
                         tyuniv = dTyUniv, tyabs = dTyAbst,
                         kindparser = kindparser} true
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




end
