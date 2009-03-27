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
type kind = Kind.kind
type hol_type = Type.hol_type

open Portable Feedback optmonad;
infix >> >-;

val ERR = mk_HOL_ERR "ParseDatatype";
val ERRloc = mk_HOL_ERRloc "ParseDatatype";

fun kcheck_say s = if Feedback.current_trace "show_typecheck_errors" > 0 handle _ => true
                   then Lib.say s else ()

datatype kcheck_error =
         TyAppFail of hol_type * hol_type
       | TyUnivFail of hol_type
       | TyKindConstrFail of hol_type * kind
       | TyRankConstrFail of hol_type * int
       | TyRankLEConstrFail of hol_type * int

val last_kcerror : kcheck_error option ref = ref NONE

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

(*
fun pretypeToType pty =
  case pty of
    dVartype (s,kd,rk) => Type.mk_vartype_opr (s, Prekind.toKind kd, Prerank.toRank rk)
  | dContype {Thy=SOME Thy,Tyop,Kind,Rank} => Type.mk_thy_con_type {Thy=Thy, Tyop=Tyop, Kind=Kind, Rank=Rank}
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
*)

fun list_dTyApp (opr,[]) = opr
  | list_dTyApp (opr,arg::args) = list_dTyApp(dTyApp(opr,arg), args)

fun strip_dTyApp ty =
  let fun strip (dTyApp(opr,arg)) acc = strip opr (arg::acc)
        | strip ty acc = (ty,acc)
  in strip ty []
  end


(* returns a list of strings, names of all kind variables mentioned *)
fun kindvars ty =
  case ty of
    dVartype (_, kd, _) => Prekind.kindvars kd
  | dContype{Kind=Kind, ...} => Prekind.kindvars Kind
  | dTyApp (ty1, ty2) => Lib.union (kindvars ty1) (kindvars ty2)
  | dTyUniv (tyv, ty) => Lib.union (kindvars tyv) (kindvars ty)
  | dTyAbst (tyv, ty) => Lib.union (kindvars tyv) (kindvars ty)
  | dTyKindConstr {Ty,Kind} => Lib.union (kindvars Ty) (Prekind.kindvars Kind)
  | dTyRankConstr {Ty,... } => kindvars Ty
  | dAQ (Ty) => map Kind.dest_var_kind (Type.kind_vars Ty)

(* returns a list of strings, names of all type variables mentioned *)
local
fun app_tri f g (x,y,z) = (x, f y, g z)
in
fun tyvars ty =
  case ty of
    dVartype (v as (s, kd, rk)) => [v]
  | dContype s => []
  | dTyApp (ty1, ty2) => Lib.union (tyvars ty1) (tyvars ty2)
  | dTyUniv (tyv, ty) => Lib.subtract (tyvars ty) (tyvars tyv)
  | dTyAbst (tyv, ty) => Lib.subtract (tyvars ty) (tyvars tyv)
  | dTyKindConstr {Ty,...} => tyvars Ty
  | dTyRankConstr {Ty,...} => tyvars Ty
  | dAQ (Ty) => map ((app_tri Prekind.fromKind Prerank.fromRank) o Type.dest_vartype_opr)
                    (Type.type_vars Ty)
end

fun list_union f [] = []
  | list_union f (x::xs) = Lib.union (f x) (list_union f xs)

fun field_kindvars (str,pty)         = kindvars pty
fun constructor_kindvars (str, ptys) = list_union kindvars ptys
fun form_kindvars (Constructors cns) = list_union constructor_kindvars cns
  | form_kindvars (Record flds)      = list_union field_kindvars flds
fun ast_kindvars (str,form) = form_kindvars form
fun asts_kindvars asts = list_union ast_kindvars asts

fun field_tyvars (str,pty)         = tyvars pty
fun constructor_tyvars (str, ptys) = list_union tyvars ptys
fun form_tyvars (Constructors cns) = list_union constructor_tyvars cns
  | form_tyvars (Record flds)      = list_union field_tyvars flds
fun ast_tyvars (str,form) = form_tyvars form
fun asts_tyvars asts = list_union ast_tyvars asts

fun ast_deftypes (str,form) = [str]
fun asts_deftypes asts = list_union ast_deftypes asts


fun kind_rank_to_string (kd,rk) =
    if current_trace "kinds" = 0 then "" else
      let open Prekind Prerank
      in   (if prekind_compare(kd,typ) = EQUAL
            then "" else ":" ^ prekind_to_string kd)
         ^ (if prerank_compare(rk,Zerorank) = EQUAL
            then "" else ":<=" ^ prerank_to_string rk)
      end

datatype pp_pty_state = none | left | right

fun pp_pretype pps ty =
 let open Portable
     val {add_string,add_break,begin_block,end_block,...} = with_ppstream pps
     fun pppretype state ty =
       case ty of
           dVartype(s,kd,rk) => add_string ("V(" ^ s ^ kind_rank_to_string(kd,rk) ^ ")")
         | dContype {Thy, Tyop, Kind, Rank} =>
              (case Thy of
                  SOME Thy' => if Thy' = "bool" orelse Thy' = "min" then
                                                 add_string Tyop
                               else add_string (Thy' ^ "$" ^ Tyop)
                | NONE => add_string Tyop)
         | dTyApp(dTyApp(dContype{Tyop="fun",...}, ty1), ty2) =>
                              (if state = none then begin_block INCONSISTENT 0
                               else if state = left then
                                   (add_string "("; begin_block INCONSISTENT 0)
                               else ();
                               pppretype left ty1;
                               add_string " ->";
                               add_break(1,0);
                               pppretype right ty2;
                               if state = none then end_block()
                               else if state = left then
                                  (end_block(); add_string ")")
                               else ())
         | dTyApp(dTyApp(dContype{Tyop="prod",...}, ty1), ty2) =>
                              (if state = none then begin_block INCONSISTENT 0
                               else if state = left then
                                   (add_string "("; begin_block INCONSISTENT 0)
                               else ();
                               pppretype left ty1;
                               add_string " #";
                               add_break(1,0);
                               pppretype right ty2;
                               if state = none then end_block()
                               else if state = left then
                                  (end_block(); add_string ")")
                               else ())
         | dTyApp(dTyApp(dContype{Tyop="sum",...}, ty1), ty2) =>
                              (if state = none then begin_block INCONSISTENT 0
                               else if state = left then
                                   (add_string "("; begin_block INCONSISTENT 0)
                               else ();
                               pppretype left ty1;
                               add_string " +";
                               add_break(1,0);
                               pppretype right ty2;
                               if state = none then end_block()
                               else if state = left then
                                  (end_block(); add_string ")")
                               else ())
         | dTyApp(ty1, ty2) => (add_string "(";
                               begin_block INCONSISTENT 0;
                               pppretype none ty2;
                               add_break(1,0);
                               pppretype none ty1;
                               end_block();
                               add_string ")")
         | dTyUniv(tyv, ty) => (add_string "(!";
                               begin_block INCONSISTENT 0;
                               pppretype none tyv;
                               add_string ".";
                               add_break(1,2);
                               pppretype none ty;
                               end_block();
                               add_string ")")
         | dTyAbst(tyv, ty) => (add_string "(\\";
                               begin_block INCONSISTENT 0;
                               pppretype none tyv;
                               add_string ".";
                               add_break(1,2);
                               pppretype none ty;
                               end_block();
                               add_string ")")
         | dTyKindConstr {Ty, Kind} =>
                              (begin_block INCONSISTENT 0;
                               pppretype none Ty;
                               add_string " :";
                               add_break(1,2);
                               add_string (HolKernel.kind_to_string(Prekind.toKind Kind));
                               end_block())
         | dTyRankConstr {Ty, Rank} =>
                              (begin_block INCONSISTENT 0;
                               pppretype none Ty;
                               add_string " :<=";
                               add_break(1,2);
                               add_string (Int.toString(Prerank.toRank Rank));
                               end_block())
         | dAQ (ty) => Parse.pp_type pps ty
 in
   pppretype none ty
 end;

val pretype_to_string = Portable.pp_to_string 80 pp_pretype
fun print_pretype ty = Portable.output(Portable.std_out, pretype_to_string ty);


local open Type
in
fun fromType t =
  if is_vartype t then let
      val (str, kd, rk) = dest_vartype_opr t
    in
      dVartype (str, Prekind.fromKind kd, Prerank.fromRank rk)
    end
  else if is_con_type t then let
      val {Thy, Tyop, Kind, Rank} = dest_thy_con_type t
    in
      dContype {Kind=Prekind.fromKind Kind,
                Rank=Prerank.fromRank Rank,
                Thy=SOME Thy, Tyop=Tyop}
    end
  else if is_app_type t then let
      val (ty1, ty2) = Type.dest_app_type t
    in
      dTyApp(fromType ty1, fromType ty2)
    end
  else if is_univ_type t then let
      val (ty1, ty2) = Type.dest_univ_type t
    in
      dTyUniv(fromType ty1, fromType ty2)
    end
  else if is_abs_type t then let
      val (ty1, ty2) = Type.dest_abs_type t
    in
      dTyAbst(fromType ty1, fromType ty2)
    end
  else raise ERR "fromType" "Unexpected sort of type"
end




fun remove_made_links ty =
  case ty of
    dVartype(s,kd,rk) => dVartype(s, Prekind.remove_made_links kd,
                                     Prerank.remove_made_links rk)
  | dContype {Thy, Tyop, Kind, Rank} =>
      dContype {Kind=Prekind.remove_made_links Kind, Thy=Thy, Tyop=Tyop,
                  Rank=Prerank.remove_made_links Rank}
  | dTyApp(ty1, ty2) => dTyApp (remove_made_links ty1, remove_made_links ty2)
  | dTyUniv(tyv, ty) => dTyUniv(remove_made_links tyv, remove_made_links ty)
  | dTyAbst(tyv, ty) => dTyAbst(remove_made_links tyv, remove_made_links ty)
  | dTyKindConstr {Ty, Kind} =>
      dTyKindConstr {Ty=remove_made_links Ty, Kind=Prekind.remove_made_links Kind}
  | dTyRankConstr {Ty, Rank} =>
      dTyRankConstr {Ty=remove_made_links Ty, Rank=Prerank.remove_made_links Rank}
  | _ => ty (* including dAQ *)

val tyvariant = Lexis.gen_variant Lexis.tyvar_vary

fun kind_replace_null_links kd (kenv,tenv) =
    let val (kenv', result) = Prekind.replace_null_links kd kenv
    in ((kenv',tenv), result)
    end

(* eta-expansion (see "env" after end below) *is* necessary *)
fun replace_null_links ty env = let
in
  case ty of
    dTyApp (ty1,ty2) => replace_null_links ty1 >> replace_null_links ty2 >> ok
  | dTyUniv (tyv, ty) => replace_null_links tyv >> replace_null_links ty >> ok
  | dTyAbst (tyv, ty) => replace_null_links tyv >> replace_null_links ty >> ok
  | dTyKindConstr {Ty,Kind} => replace_null_links Ty >> kind_replace_null_links Kind >> ok
  | dTyRankConstr {Ty,Rank} => replace_null_links Ty >> ok
  | dVartype (s,kd,rk) => kind_replace_null_links kd
  | dContype {Thy,Tyop,Kind,Rank} => kind_replace_null_links Kind
  | dAQ (Ty) => ok
end env

val op ==> = Prekind.==>

fun list_mk_arrow_kind([], kd0) = kd0
  | list_mk_arrow_kind(kd::kds, kd0) = kd ==> list_mk_arrow_kind(kds, kd0)

fun clean deftys params pty =
let val pkinds = map #2 params
    val par_types = map (fn (s,kd,rk) => Type.mk_vartype_opr(s, Prekind.toKind kd, Prerank.toRank rk)) params
    fun clean pty =
(case pty of
    dVartype (s,kd,rk) => Type.mk_vartype_opr (s, Prekind.toKind kd, Prerank.toRank rk)
  | dContype {Thy,Tyop,Kind,Rank} =>
      let val is_defty = Lib.mem Tyop deftys
          val Kind' = if is_defty then list_mk_arrow_kind(pkinds, Kind)
                                  else Kind
          val cty = (case Thy of
                        SOME Thy' => Type.mk_thy_con_type {Thy=Thy', Tyop=Tyop,
                                           Kind=Prekind.toKind Kind', Rank=Prerank.toRank Rank}
                      | NONE      => Type.mk_con_type {Tyop=Tyop,
                                           Kind=Prekind.toKind Kind', Rank=Prerank.toRank Rank})
                     handle HOL_ERR _ => (* This can happen during error messages from kind inference *)
                      Feedback.trace ("Vartype Format Complaint",0)
                         Type.mk_vartype_opr(Tyop, Prekind.toKind Kind', Prerank.toRank Rank)
      in if is_defty then Type.list_mk_app_type(cty, par_types)
                     else cty
      end
  | dTyApp(ty1,ty2)  => (Type.mk_app_type  (clean ty1, clean ty2)
                          handle Feedback.HOL_ERR e =>
                            (print ("Applying " ^ HolKernel.type_to_string (clean ty1)
                                       ^ " to " ^ HolKernel.type_to_string (clean ty2) ^ "\n");
                             raise Feedback.mk_HOL_ERR "Pretype" "clean" (#message e)))
  | dTyUniv (tyv,ty) => Type.mk_univ_type (clean tyv, clean ty)
  | dTyAbst (tyv,ty) => Type.mk_abs_type  (clean tyv, clean ty)
  | dTyKindConstr {Ty,Kind} => clean Ty
  | dTyRankConstr {Ty,Rank} => clean Ty
  | dAQ (Ty) => Ty
) handle e => raise (wrap_exn "ParseDatatype.clean" (pretype_to_string pty) e)
in clean pty
end

fun def_toType deftys ftyvs ty =
  let (* val ty = if Feedback.current_trace "beta_conv_types" > 0
                      then deep_beta_conv_ty ty
                      else ty *)
      val _ = replace_null_links ty (kindvars ty, (map #1 o tyvars) ty)
  in
    clean deftys ftyvs (remove_made_links ty)
  end
  handle e => raise (wrap_exn "ParseDatatype" "toType" e)

fun toType ty = def_toType [] [] ty

fun field_remove_made_links (str,pty) = (str, remove_made_links pty)
fun constructor_remove_made_links (str,ptys) = (str, map remove_made_links ptys)
fun form_remove_made_links form =
  case form of
    Constructors cns => Constructors (map constructor_remove_made_links cns)
  | Record flds => Record (map field_remove_made_links flds)
fun ast_remove_made_links (str,form) = (str, form_remove_made_links form)
fun asts_remove_made_links asts = map ast_remove_made_links asts

(* eta-expansion (see "env" after end below) *is* necessary *)
fun list_replace item_replace [] env = ok env
  | list_replace item_replace (x::xs) env = (item_replace x >> list_replace item_replace xs >> ok) env

fun field_replace_null_links (str,pty) = replace_null_links pty
fun constructor_replace_null_links (str,ptys) = list_replace replace_null_links ptys
(* eta-expansion (see "env" after end below) *is* necessary *)
fun form_replace_null_links form env = let
in
  case form of
    Constructors cns => list_replace constructor_replace_null_links cns
  | Record flds      => list_replace field_replace_null_links flds
end env
fun ast_replace_null_links (str,form) = form_replace_null_links form
fun asts_replace_null_links asts = list_replace ast_replace_null_links asts

(*
fun cleanField (str,pty) = (str, clean pty)
fun cleanConstructor (str,ptys) = (str, map clean ptys)

fun cleanForm (Constructors cns) = Constructors (map cleanConstructor cns)
  | cleanForm (Record flds)      = Record (map cleanField flds)

fun cleanAST (str,form) = (str, cleanForm form)
fun cleanASTs asts = map cleanAST asts
*)

fun toASTs asts =
  let val _ = asts_replace_null_links asts (asts_kindvars asts, (map #1 o asts_tyvars) asts)
  in
    (*cleanASTs*) (asts_remove_made_links asts)
  end
  handle e => raise (wrap_exn "ParseDatatype" "toASTs" e)


(*---------------------------------------------------------------------------*
 * Calculate the prekind or prerank of a pretype.                            *
 *---------------------------------------------------------------------------*)

fun pkind_of (*deftys par_kds*) ty = let
  fun pkd (dVartype(s,kd,rk)) = kd
    | pkd (dContype{Tyop, Kind, ...}) = (*if Lib.mem Tyop deftys
                                        then list_mk_arrow_kind(par_kds, Kind)
                                        else*) Kind
    | pkd (dTyApp(opr,arg)) = Prekind.chase (pkd opr)
    | pkd (dTyUniv _) = Prekind.typ
    | pkd (dTyAbst(Bvar,Body)) = pkd Bvar ==> pkd Body
    | pkd (dTyKindConstr{Ty,Kind}) = Kind
    | pkd (dTyRankConstr{Ty,Rank}) = pkd Ty
    | pkd (dAQ(Ty)) = Prekind.fromKind (Type.kind_of Ty)
in pkd ty
end


local
val zero = Prerank.Zerorank
val inc  = Prerank.Sucrank
val max  = Prerank.mk_Maxrank
in
fun prank_of (dVartype(s,kd,rk)) = rk
  | prank_of (dContype{Rank, ...}) = Rank
  | prank_of (dTyApp(opr,arg))     = max(    prank_of opr  , prank_of arg )
  | prank_of (dTyUniv(Bvar,Body))  = max(inc(prank_of Bvar), prank_of Body)
  | prank_of (dTyAbst(Bvar,Body))  = max(    prank_of Bvar , prank_of Body)
  | prank_of (dTyKindConstr{Ty,Kind}) = prank_of Ty
  | prank_of (dTyRankConstr{Ty,Rank}) = Rank
  | prank_of (dAQ(Ty)) = Prerank.fromRank (Type.rank_of Ty)
end;


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

fun mk_conty{Thy,Tyop,Kind,Rank,Locn} =
       dContype{Thy=SOME Thy,Tyop=Tyop,Kind=Kind,Rank=Rank}

fun parse_type strm =
  parse_type.parse_type {vartype = dVartype o #1, tyop = tyop, qtyop = qtyop,
                         antiq = dAQ, kindcast = kindcast, rankcast = rankcast,
                         tycon = mk_conty, tyapp = dTyApp,
                         tyuniv = dTyUniv, tyabs = dTyAbst,
                         kindparser = kindparser} true
  (Parse.type_grammar()) strm


(*---------------------------------------------------------------------------
       Parsing environments
 ---------------------------------------------------------------------------*)

type env = {scope_ty : (string * (prekind * prerank)) list,
            free_ty  : (string * (prekind * prerank)) list};

fun lookup_ftyvar(s,({free_ty,...}:env)) = Lib.assoc s free_ty;
fun lookup_btyvar(s,({scope_ty,...}:env)) = Lib.assoc s scope_ty;
fun add_free_ty ((s,kd,rk),{scope_ty,free_ty}) =
    {scope_ty=scope_ty, free_ty=(s,(kd,rk))::free_ty}
fun add_scope_ty((s,kd,rk),{scope_ty,free_ty}) =
    {scope_ty=(s,(kd,rk))::scope_ty, free_ty=free_ty};

val empty_env = {scope_ty=[], free_ty=[]};
fun get_env (e:env) = e;

type pretype_in_env = env -> pretype * env

fun cdomkd M [] = M
  | cdomkd (dTyUniv(Bvar,Body)) (kd::rst) =
       dTyUniv(dTyKindConstr{Ty=Bvar,Kind=kd}, cdomkd Body rst)
  | cdomkd (dTyAbst(Bvar,Body)) (kd::rst) =
       dTyAbst(dTyKindConstr{Ty=Bvar,Kind=kd}, cdomkd Body rst)
  | cdomkd x y = raise ERR "cdomkd" "missing case";

fun cdomfkd (f,e) kd = ((fn ty => cdomkd (f ty) [kd]), e)

fun make_kind_binding_occ bty kd E = cdomfkd (bty E) kd;

fun cdomrk M [] = M
  | cdomrk (dTyUniv(Bvar,Body)) (rk::rst) =
       dTyUniv(dTyRankConstr{Ty=Bvar,Rank=rk}, cdomrk Body rst)
  | cdomrk (dTyAbst(Bvar,Body)) (rk::rst) =
       dTyAbst(dTyRankConstr{Ty=Bvar,Rank=rk}, cdomrk Body rst)
  | cdomrk x y = raise ERR "cdomrk" "missing case";

fun cdomfrk (f,e) rk = ((fn ty => cdomrk (f ty) [rk]), e)

fun make_rank_binding_occ bty rk E = cdomfrk (bty E) rk;


(*---------------------------------------------------------------------------
 * Free occurrences of variables.
 *---------------------------------------------------------------------------*)

fun make_free_tyvar ((s,kd,rk),E) = let
  fun fresh (s,kd,rk,E) = let
    val v = (s, kd, rk)
  in
    (dVartype v, add_free_ty(v, E))
  end
in
       let val (kd, rk) = lookup_ftyvar(s,E)
       in (dVartype(s, kd, rk), E)
       end
       handle HOL_ERR _ => fresh(s,kd,rk,E)
end

(*---------------------------------------------------------------------------
 * Bound occurrences of variables.
 *---------------------------------------------------------------------------*)

fun make_btyvar (s,E) =
    let val (kind,rank) = lookup_btyvar(s,E)
    in (dVartype(s,kind,rank), E)
    end;

fun make_type_atom (s,kd,rk) E =
 make_btyvar (s,E)
   handle HOL_ERR _ =>
   make_free_tyvar ((s,kd,rk), E)


fun make_type_constant {Thy=Thy0,Tyop=Tyop0} E =
 let val c = case Thy0 of
                   SOME Thy' => Type.prim_mk_thy_con_type {Thy=Thy',Tyop=Tyop0}
                 | NONE      => Type.prim_mk_con_type Tyop0
     val {Thy,Tyop,Kind,Rank} = Type.dest_thy_con_type c
     val Kind' = Prekind.rename_kindvars [] (Prekind.fromKind Kind)
     val Rank' = Prerank.fromRank Rank
 in (dContype {Thy=SOME Thy,Tyop=Tyop,Kind=Kind',Rank=Rank'}, E)
 end
 handle Feedback.HOL_ERR _ =>
 let val Kind' = Prekind.new_uvar()
     val Rank' = Prerank.new_uvar()
 in (dContype {Thy=Thy0,Tyop=Tyop0,Kind=Kind',Rank=Rank'}, E)
 end


(*---------------------------------------------------------------------------
 * Combs
 *---------------------------------------------------------------------------*)

fun list_make_app_type (ty1::(rst as (_::_))) E =
     Lib.rev_itlist (fn ty => fn (tyop,e) =>
        let val (ty',e') = ty e
        in (dTyApp(tyop, ty'), e') end)
     rst (ty1 E)
  | list_make_app_type _ _ = raise ERR "list_make_app_type" "insufficient args";

(*---------------------------------------------------------------------------
 * Constraints
 *---------------------------------------------------------------------------*)

fun make_kind_constr_type ty kd E = let
  val (ty',E') = ty E
in
  (dTyKindConstr{Ty = ty', Kind = kd}, E')
end;

fun make_rank_constr_type ty rk E = let
  val (ty',E') = ty E
in
  (dTyRankConstr{Ty = ty', Rank = rk}, E')
end;

(*---------------------------------------------------------------------------

  Abstractions, qualified abstractions, and vstructs.

  The thing to know about parsing abstractions is that an abstraction is
  a function from the string identifying the binder to an env to a
  pair. The first member of the pair is a function that will take the
  body of the abstraction and produce a lambda term, essentially by
  clapping on whatever variables, or applying whatever constants
  necessary. The second member of the pair is the environment previous
  to entering the abstraction plus whatever new free variables were
  found in the body of the abstraction.

  We could just return (F tm', E), except that we may add free variables
  found in tm to E.
 ----------------------------------------------------------------------------*)

fun bind_type alist ty (E as {scope_ty=scope_ty0,...}:env) : (pretype*env) = let
  fun itthis a (e,f) = let 
    val (g,e') = a e 
  in 
    (e', f o g) 
  end
  val (E',F) = Lib.rev_itlist itthis alist (E,Lib.I)
  val (ty',({free_ty=free_ty1,...}:env)) = ty E'
in
  (F ty', {scope_ty=scope_ty0,free_ty=free_ty1})
end;


fun make_binding_type_occ s binder E =
 let val _ =
       Lexis.allowed_user_type_var s orelse
       raise ERR "make_binding_type_occ"
         (s ^ " is not lexically permissible as a binding type variable")
     val nkv = Prekind.new_uvar()
     val nrv = Prerank.new_uvar()
     val pty = dVartype(s, nkv, nrv)
     val E' = add_scope_ty((s,nkv,nrv),E)
 in
  case binder
   of "\\" => ((fn b => dTyAbst(pty,b)), E')
    | "!"  => ((fn b => dTyUniv(pty,b)), E')
    |  _   => raise ERR "make_binding_type_occ" ("invalid binder: " ^ binder)
 end;


fun to_ptyInEnv ty = let
  fun binder_type binder (dVartype(s,kd,rk)) = make_binding_type_occ s binder
    | binder_type binder (dTyKindConstr{Ty,Kind}) =
            make_kind_binding_occ (binder_type binder Ty) Kind
    | binder_type binder (dTyRankConstr{Ty,Rank}) =
            make_rank_binding_occ (binder_type binder Ty) Rank
    | binder_type _ _ = raise ERR "to_ptyInEnv" "non-variable type binder"
in case ty of
     dVartype(s,kd,rk)  => make_type_atom (s,kd,rk)
   | dContype{Thy,Tyop,Kind,Rank} => make_type_constant {Thy=Thy,Tyop=Tyop}
   | dTyApp(ty1,ty2   ) => list_make_app_type (map to_ptyInEnv [ty1,ty2])
   | dTyUniv(bvar,body) => bind_type [binder_type "!"  bvar] (to_ptyInEnv body)
   | dTyAbst(bvar,body) => bind_type [binder_type "\\" bvar] (to_ptyInEnv body)
   | dTyKindConstr{Ty,Kind}     => make_kind_constr_type (to_ptyInEnv Ty) Kind
   | dTyRankConstr{Ty,Rank}     => make_rank_constr_type (to_ptyInEnv Ty) Rank
   | dAQ(Ty)                    => to_ptyInEnv (fromType Ty)
end

fun to_listInEnv to_itemInEnv   []    E = ([],E)
  | to_listInEnv to_itemInEnv (x::xs) E =
      let val (x', E1) = to_itemInEnv x E
          val (xs',E2) = to_listInEnv to_itemInEnv xs E1
      in (x'::xs', E2)
      end

fun to_strpairInEnv to_itemInEnv (str,item) E =
      let val (item',E') = to_itemInEnv item E
      in ((str,item'), E')
      end

val to_fieldInEnv        = to_strpairInEnv to_ptyInEnv
val to_constructorInEnv  = to_strpairInEnv (to_listInEnv to_ptyInEnv)
val to_fieldsInEnv       = to_listInEnv to_fieldInEnv
val to_constructorsInEnv = to_listInEnv to_constructorInEnv

fun make_constructors cns E =
  let val (cns',E') = cns E
  in (Constructors cns', E')
  end

fun make_record rcd E =
  let val (rcd',E') = rcd E
  in (Record rcd', E')
  end

fun to_formInEnv (Constructors cns) = make_constructors (to_constructorsInEnv cns)
  | to_formInEnv (Record flds)      = make_record (to_fieldsInEnv flds)

val to_ASTInEnv  = to_strpairInEnv to_formInEnv
val to_ASTsInEnv = to_listInEnv to_ASTInEnv



(*---------------------------------------------------------------------------
 * Kind inference for HOL types. Looks ugly because of error messages, but is
 * actually very simple, given side-effecting unification.
 *---------------------------------------------------------------------------*)

fun is_atom (dVartype _) = true
  | is_atom (dContype _) = true
  | is_atom (dTyKindConstr{Ty,...}) = is_atom Ty
  | is_atom (dTyRankConstr{Ty,...}) = is_atom Ty
  | is_atom (dAQ Ty) = Type.is_vartype Ty orelse Type.is_con_type Ty
  | is_atom ty = false



local
  fun default_kdprinter x = "<kind>"
  fun default_typrinter x = "<hol_type>"
in
fun KC printers deftys params = let
  val prk = Int.toString
  val (pty, pkd) =
      case printers
       of SOME (y,z) =>
          let val kdprint = z
              fun typrint ty =
                  if Type.is_con_type ty
                  then (y ty ^ " : " ^ z (Type.kind_of ty)
                             ^ " :<= " ^ prk (Type.rank_of ty))
                  else y ty
          in
            (typrint, kdprint)
          end
        | NONE => (default_typrinter, default_kdprinter)
  fun check(dTyApp(opr,arg)) =
      (check opr;
       check arg;
       Prekind.unify (pkind_of opr)
                     (pkind_of arg ==> Prekind.new_uvar())
       handle (e as Feedback.HOL_ERR{origin_structure="Prekind",
                                     origin_function="unify",message})
       => let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 2
              val opr' = def_toType deftys params opr
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val arg' = def_toType deftys params arg
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val message =
                  String.concat
                      [
                       "\nKind inference failure: unable to infer a kind \
                       \for the application of\n\n",
                       pty opr',
                       "\n\n",
                       if (is_atom opr) then ""
                       else ("which has kind\n\n" ^
                             pkd(Type.kind_of opr') ^ "\n\n"),

                       "to\n\n",
                       pty arg',
                       "\n\n",

                       if (is_atom arg) then ""
                       else ("which has kind\n\n" ^
                             pkd(Type.kind_of arg') ^ "\n\n"),

                       "kind unification failure message: ", message, "\n"]
          in
            Feedback.set_trace "kinds" tmp;
            kcheck_say message;
            last_kcerror := SOME (TyAppFail(opr',arg'));
            raise ERR "kindcheck" "failed"
          end)
    | check (dTyUniv(Bvar, Body)) =
       (check Bvar; check Body; Prekind.unify (pkind_of Body) Prekind.typ
       handle (e as Feedback.HOL_ERR{origin_structure="Prekind",
                                     origin_function="unify",message})
       => let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 2
              val real_type = def_toType deftys params Body
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val real_kind = Prekind.toKind Prekind.typ
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val message =
                  String.concat
                      [
                       "\nKind inference failure: the type\n\n",
                       pty real_type,
                       "\n\n",
                       if (is_atom Body) then ""
                       else ("which has kind\n\n" ^
                             pkd(Type.kind_of real_type) ^ "\n\n"),

                       "can not be constrained to be of kind\n\n",
                       pkd real_kind,

                       "kind unification failure message: ", message, "\n"]
          in
            Feedback.set_trace "kinds" tmp;
            kcheck_say message;
            last_kcerror := SOME (TyUnivFail(real_type));
            raise ERR "kindcheck" "failed"
          end)
    | check (dTyAbst(Bvar, Body)) = (check Bvar; check Body)
    | check (dTyKindConstr{Ty,Kind}) =
       (check Ty; Prekind.unify (pkind_of Ty) Kind
       handle (e as Feedback.HOL_ERR{origin_structure="Prekind",
                                     origin_function="unify",message})
       => let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 2
              val real_type = def_toType deftys params Ty
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val real_kind = Prekind.toKind Kind
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val message =
                  String.concat
                      [
                       "\nKind inference failure: the type\n\n",
                       pty real_type,
                       "\n\n",
                       if (is_atom Ty) then ""
                       else ("which has kind\n\n" ^
                             pkd(Type.kind_of real_type) ^ "\n\n"),

                       "can not be constrained to be of kind\n\n",
                       pkd real_kind,
                       "\n\n",

                       "kind unification failure message: ", message, "\n"]
          in
            Feedback.set_trace "kinds" tmp;
            kcheck_say message;
            last_kcerror := SOME (TyKindConstrFail(real_type, real_kind));
            raise ERR "kindcheck" "failed"
          end)
    | check (dTyRankConstr{Ty,Rank}) =
       (check Ty; Prerank.unify (prank_of Ty) Rank
       handle (e as Feedback.HOL_ERR{origin_structure="Prerank",
                                     origin_function="unify",message})
       => let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 2
              val real_type = def_toType deftys params Ty
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val real_rank = Prerank.toRank Rank
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val message =
                  String.concat
                      [
                       "\nRank inference failure: the type\n\n",
                       pty real_type,
                       "\n\n",
                       if (is_atom Ty) then ""
                       else ("which has rank " ^
                             prk(Type.rank_of real_type) ^ "\n\n"),

                       "can not be constrained to be of rank ",
                       prk real_rank, "\n\n",

                       "rank unification failure message: ", message, "\n"]
          in
            Feedback.set_trace "kinds" tmp;
            kcheck_say message;
            last_kcerror := SOME (TyRankConstrFail(real_type, real_rank));
            raise ERR "rankcheck" "failed"
          end
       | (e as Feedback.HOL_ERR{origin_structure="Prerank",
                                     origin_function="unify_le",message})
       => let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 2
              val real_type = def_toType deftys params Ty
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val real_rank = Prerank.toRank Rank
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val message =
                  String.concat
                      [
                       "\nRank inference failure: the type\n\n",
                       pty real_type,
                       "\n\n",
                       if (is_atom Ty) then ""
                       else ("which has rank " ^
                             prk(Type.rank_of real_type) ^ "\n\n"),

                       "can not be constrained to be <= rank ",
                       prk real_rank, "\n\n",

                       "rank unification failure message: ", message, "\n"]
          in
            Feedback.set_trace "kinds" tmp;
            kcheck_say message;
            last_kcerror := SOME (TyRankLEConstrFail(real_type, real_rank));
            raise ERR "rankcheck" "failed"
          end)
    | check _ = ()
  fun checkTyp Ty = check Ty (* (dTyKindConstr{Ty=Ty,Kind=Prekind.typ}) *)
  fun checkList ckfn ([]) = ()
    | checkList ckfn (x::xs) = (ckfn x; checkList ckfn xs)
  fun checkField(str,pty) = checkTyp pty
  fun checkConstructor(str,ptys) = checkList checkTyp ptys
  fun checkForm(Constructors cns) = checkList checkConstructor cns
    | checkForm(Record flds) = checkList checkField flds
  fun checkAST(str,form) = checkForm form
in checkList checkAST
end end;

fun kindcheck pfns ast = let
  val params = Lib.sort (fn u => fn v => String.<(#1 u, #1 v)) (asts_tyvars ast)
  val deftys = asts_deftypes ast
  val _ = KC pfns deftys params ast
in
  ast
end

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

fun make_asts asts_in_e = Lib.fst(asts_in_e empty_env)

fun parse q = let
  val strm = qbuf.new_buffer q
  val result0 = sepby1 ";" parse_G strm
  val pfns = SOME(Parse.type_to_string, Parse.kind_to_string)
  val result = kindcheck pfns (make_asts (to_ASTsInEnv result0))
in
  case qbuf.current strm of
    (base_tokens.BT_EOI,_) => toASTs result
  | (_,locn) => raise ERRloc "parse" locn
                             "Parse failed"
end




end
