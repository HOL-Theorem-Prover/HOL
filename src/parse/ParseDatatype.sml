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

fun consume P (qb,s,locn) = let
  open base_tokens
  (* know first char of s is OK wrt P *)
  fun grab i =
      if i = size s then i
      else if P (String.sub(s,i)) then grab (i + 1)
      else i
  val alphapfx_len = grab 1
  val pfx = String.substring(s,0,alphapfx_len)
  val sfx = String.extract(s,alphapfx_len,NONE)
in
  if sfx = "" then ((fn () => qbuf.advance qb), pfx, locn)
  else let
      val (locn',locn'') = locn.split_at (size pfx) locn
    in
      ((fn () => qbuf.replace_current (BT_Ident sfx,locn'') qb), pfx, locn')
    end
end

fun okident c = Char.isAlphaNum c orelse c = #"'" orelse c = #"_"

fun ident_munge dollared qb s locn = let
  val s0 = String.sub(s, 0)
in
  if Char.isAlpha s0 then let
      val (adv, pfx, locn') = consume okident (qb,s,locn)
    in
      if pfx <> "of" orelse dollared then (adv(); pfx)
      else raise ERRloc "ident" locn
                        "Expected an identifier, got (reserved word) \"of\""
    end
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
      else raise ERRloc "ident" locn
                        (s ^ " not a valid constructor/field/type name")
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
    if Char.isAlpha (String.sub(s, 0)) then let
        val (adv,idstr,locn') = consume Char.isAlphaNum (qb,s,locn)
      in
        (adv,BT_Ident idstr,locn')
      end
    else let
        fun oksym c = Char.isPunct c andalso c <> #"(" andalso c <> #")" andalso
                      c <> #"'"
        val (adv,idstr,locn') = consume oksym (qb,s,locn)
      in
        (adv,BT_Ident idstr,locn')
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

fun qtyop {Tyop, Thy, Locn, Args} =
    dTyop {Tyop = Tyop, Thy = SOME Thy, Args = Args}
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

(*
fun to_ptyInEnv ty = let
  open Pretype Parse_support
  fun binder_type binder (Pretype.PT(Pretype.Vartype(s,kd,rk),l)) = make_binding_type_occ l s binder
    | binder_type binder (Pretype.PT(Pretype.TyKindConstr{Ty,Kind},l)) =
            make_kind_binding_occ l (binder_type binder Ty) Kind
    | binder_type binder (Pretype.PT(Pretype.TyRankConstr{Ty,Rank},l)) =
            make_rank_binding_occ l (binder_type binder Ty) Rank
    | binder_type _ _ = raise ERROR "to_ptyInEnv" "non-variable type binder"
in case ty of
     dVartype(s,kd,rk)  => make_type_atom l (s,kd,rk)
   | dContype{Thy,Tyop,Kind,Rank} => make_type_constant l {Thy=Thy,Tyop=Tyop}
   | dTyApp(ty1,ty2   ) => list_make_app_type l (map to_ptyInEnv [ty1,ty2])
   | dTyUniv(bvar,body) => bind_type l [binder_type "!"  bvar] (to_ptyInEnv body)
   | dTyAbst(bvar,body) => bind_type l [binder_type "\\" bvar] (to_ptyInEnv body)
   | dTyKindConstr{Ty,Kind}     => make_kind_constr_type l (to_ptyInEnv Ty) Kind
   | dTyRankConstr{Ty,Rank}     => make_rank_constr_type l (to_ptyInEnv Ty) Rank
   | dAQ(Ty)                    => 
end

fun parse_type strm =
   let val pty = parse_type0 strm
       val pfns = SOME(Parse.type_to_string, Parse.kind_to_string)
   in
     (* Pretype.kindcheck pfns (Parse_support.make_pretype (Parse.to_ptyInEnv pty)) *)
     Pretype.kindcheck pfns (Parse_support.make_pretype (Parse.to_ptyInEnv pty))
   end
*)

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
  case pdtok_of qb of
    (_,base_tokens.BT_Ident "of",_) => let
      val _ = qbuf.advance qb
      val optargs = sepby1 "=>" parse_type qb
    in
      (constr_id, optargs)
    end
  | _ => (constr_id, [])
end

fun parse_form qb =
    case pdtok_of qb of
      (_,base_tokens.BT_Ident "<|",_) => Record (parse_record_defn qb)
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
