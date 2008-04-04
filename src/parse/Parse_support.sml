structure Parse_support :> Parse_support =
struct

type prekind = Prekind.prekind
type prerank = Prerank.prerank
type pretype = Pretype.pretype
type uvartype = Pretype.uvartype
type preterm = Preterm.preterm
type term    = Term.term

open HolKernel GrammarSpecials;

val ERROR = mk_HOL_ERR "Parse_support";
val ERRORloc = mk_HOL_ERRloc "Parse_support";

val NONEU = Pretype.NONEU;
val SOMEU = Pretype.SOMEU;

(*---------------------------------------------------------------------------
       Parsing environments
 ---------------------------------------------------------------------------*)

type env = {scope    : (string * pretype) list,
            free     : (string * pretype) list,
            scope_ty : (string * (prekind * prerank)) list,
            free_ty  : (string * (prekind * prerank)) list };

fun lookup_fvar(s,({free,...}:env)) = assoc s free;
fun lookup_bvar(s,({scope,...}:env)) = assoc s scope;
fun add_free(b,{scope,free,scope_ty,free_ty}) =
    {scope=scope, free=b::free, scope_ty=scope_ty, free_ty=free_ty}
fun add_scope(b,{scope,free,scope_ty,free_ty}) =
    {scope=b::scope, free=free, scope_ty=scope_ty, free_ty=free_ty};

fun lookup_ftyvar(s,({free_ty,...}:env)) = assoc s free_ty;
fun lookup_btyvar(s,({scope_ty,...}:env)) = assoc s scope_ty;
fun add_free_ty ((s,kd,rk),{scope,free,scope_ty,free_ty}) =
    {scope=scope, free=free, scope_ty=scope_ty, free_ty=(s,(kd,rk))::free_ty}
fun add_scope_ty((s,kd,rk),{scope,free,scope_ty,free_ty}) =
    {scope=scope, free=free, scope_ty=(s,(kd,rk))::scope_ty, free_ty=free_ty};

val empty_env = {scope=[], free=[], scope_ty=[], free_ty=[]};
fun get_env (e:env) = e;

type pretype_in_env = env -> Pretype.pretype * env
type preterm_in_env = env -> Preterm.preterm * env

(*---------------------------------------------------------------------------*
 * Denotes a binding occurrence of a variable. These are treated as          *
 * functions from preterm (the body) to preterm (the abstraction).           *
 *---------------------------------------------------------------------------*)

type btyvar_in_env = env -> (Pretype.pretype -> Pretype.pretype) * env
type bvar_in_env   = env -> (Preterm.preterm -> Preterm.preterm) * env

(*---------------------------------------------------------------------------*
 * Denotes a type variable bound by a binder ("\\" or "!").                  *
 * Hence, it takes a binder and returns a function from                      *
 * the body to a pretype (plus of course, any changes to the env).           *
 *---------------------------------------------------------------------------*)

type tybinder_in_env = string -> btyvar_in_env

(*---------------------------------------------------------------------------*
 * Denotes a variable bound by a binder ("\\" or a constant, e.g.,           *
 * "!", "?", "@"). Hence, it takes a binder and returns a function from      *
 * the body to a preterm (plus of course, any changes to the env).           *
 *---------------------------------------------------------------------------*)

type binder_in_env = string -> bvar_in_env


(*---------------------------------------------------------------------------*
 * Top level parse types                                                     *
 *---------------------------------------------------------------------------*)

fun make_pretype ty_in_e = fst(ty_in_e empty_env)

(*---------------------------------------------------------------------------*
 * Top level parse terms                                                     *
 *---------------------------------------------------------------------------*)

fun make_preterm tm_in_e = fst(tm_in_e empty_env)

(*---------------------------------------------------------------------------*
 *       Antiquotes                                                          *
 *---------------------------------------------------------------------------*)

local
  open Pretype Term Preterm
  fun from_ty l lty (E as (lscope, scope, free, scope_ty, free_ty)) =
    case lty of
      TYVAR (v as (Name,Kind,Rank)) =>
       let val pkd = Prekind.fromKind Kind
           val prk = Prerank.fromRank Rank
           val v' = (Name, pkd, prk)
       in case assoc1 Name scope_ty
           of SOME(_,(nkv,nrk)) => (Prekind.unify pkd nkv; (PT(Vartype v',l), E))
                                   (*(PT(TyRankConstr
                                         {Ty=PT(TyKindConstr
                                                  {Ty=PT(Vartype(Name,nkv,nrk),l),
                                                   Kind=pkd}, l),
                                          Rank=Rank}, l), E)*)
            | NONE => let in
               case assoc1 Name free_ty
                of NONE => (PT(Vartype v',l),
                            (lscope, scope, free, scope_ty, (Name,(pkd,prk))::free_ty))
                 | SOME(_,(nkv,nrk)) => (Prekind.unify pkd nkv; (PT(Vartype v',l), E))
                                        (*(PT(TyRankConstr
                                              {Ty=PT(TyKindConstr
                                                       {Ty=PT(Vartype(Name,nkv,nrk),l),
                                                        Kind=pkd}, l),
                                               Rank=prk}, l), E)*)
               end
       end
    | TYCONST{Thy,Tyop,Kind,Rank} =>
        (PT(Contype{Thy=Thy,Tyop=Tyop,Kind=Prekind.fromKind Kind,Rank=Prerank.fromRank Rank}, l), E)
    | TYAPP(opr,arg) =>
       let val (pty1,E1) = from_ty l (destruct_type opr) E
           val (pty2,E2) = from_ty l (destruct_type arg) E1
       in (PT(TyApp(pty1,pty2),l), E2)
       end
    | TYUNIV(bvar,body) =>
       let val (s,kd,rk) = dest_vartype_opr bvar
           val pkd = Prekind.fromKind kd
           val prk = Prerank.fromRank rk
           val v' = (s,pkd,prk)
           val (body',(_,_,_,_,free_ty')) =
                  from_ty l (destruct_type body) (lscope, scope, free, (s,(pkd,prk))::scope_ty, free_ty)
       in (PT(TyUniv(PT(Vartype v',l),body'),l), (lscope, scope, free, scope_ty, free_ty'))
       end
    | TYABS(bvar,body) =>
       let val (s,kd,rk) = dest_vartype_opr bvar
           val pkd = Prekind.fromKind kd
           val prk = Prerank.fromRank rk
           val v' = (s,pkd,prk)
           val (body',(_,_,_,_,free_ty')) =
                  from_ty l (destruct_type body) (lscope, scope, free, (s,(pkd,prk))::scope_ty, free_ty)
       in (PT(TyAbst(PT(Vartype v',l),body'),l), (lscope, scope, free, scope_ty, free_ty'))
       end

  (*fun no_l (lscope, scope, free, scope_ty, free_ty) =
         {scope=scope, free=free, scope_ty=scope_ty, free_ty=free_ty}*)
  fun from l ltm (E as (lscope, scope, free, scope_ty, free_ty)) =
    case ltm of
      VAR (v as (Name,Ty)) =>
       let val (pty,E1 as (lscope, scope, free, scope_ty, free_ty)) = (*make_aq_ty l Ty (no_l E)*)
                                                                      from_ty l (destruct_type Ty) E
                                                                      (*(Pretype.fromType Ty, E)*)
           val v' = {Name=Name, Ty=pty, Locn=l}
           fun eq {Name=Name1,Ty=Ty1,Locn=Locn1} {Name=Name2,Ty=Ty2,Locn=Locn2} =
                   Name1=Name2 andalso Pretype.eq Ty1 Ty2
       in if mem v' lscope then (Var v', E1)
          else
          case assoc1 Name scope
           of SOME(_,ntv) => (Constrained{Ptm=Var{Name=Name,Ty=ntv,Locn=l}, Ty=pty, Locn=l}, E1)
            | NONE => let in
               case assoc1 Name free
                of NONE => (Var v', (lscope, scope, (Name,pty)::free, scope_ty, free_ty))
                 | SOME(_,ntv) => (Constrained{Ptm=Var{Name=Name,Ty=ntv,Locn=l},Ty=pty,Locn=l}, E1)
               end
       end
    | CONST{Name,Thy,Ty} =>
       let val (pTy,E1 as (lscope, scope, free, scope_ty, free_ty)) = (*make_aq_ty l Ty (no_l E)*)
                                                                      from_ty l (destruct_type Ty) E
                                                                      (*(Pretype.fromType Ty, E)*)
       in (Const{Name=Name,Thy=Thy,Ty=pTy,Locn=l},E1)
       end
    | COMB(Rator,Rand)   =>
       let val (ptm1,E1) = from l (dest_term Rator) E
           val (ptm2,E2) = from l (dest_term Rand) E1
       in (Comb{Rator=ptm1, Rand=ptm2, Locn=l}, E2)
       end
    | TYCOMB(Rator,Rand)   =>
       let val (ptm,E1) = from l (dest_term Rator) E
           val (pty,E2) = (*make_aq_ty l Rand (no_l E1)*)
                          from_ty l (destruct_type Rand) E1
                          (*(Pretype.fromType Rand, E1)*)
       in (TyComb{Rator=ptm, Rand=pty, Locn=l}, E2)
       end
    | LAMB(Bvar,Body) =>
       let val (s,ty) = dest_var Bvar
           val (pty,E1 as (lscope, scope, free, scope_ty, free_ty)) = (*make_aq_ty ty (no_l E)*)
                                                                      from_ty l (destruct_type ty) E
                                                                      (*(Pretype.fromType ty, E)*)
           val v' = {Name=s, Ty = pty, Locn=l}
           val (Body',(_,_,free',scope_ty',free_ty')) =
                  from l (dest_term Body) (v'::lscope, scope, free, scope_ty, free_ty)
       in (Abs{Bvar=Var v', Body=Body', Locn=l}, (lscope, scope, free', scope_ty', free_ty'))
       end
    | TYLAMB(Bvar,Body) =>
       let val (s,kd,rk) = dest_vartype_opr Bvar
           val pkd = Prekind.fromKind kd
           val prk = Prerank.fromRank rk
           val v' = (s,pkd,prk)
           val (Body',(_,_,free',scope_ty',free_ty')) = from l (dest_term Body)
                                          (lscope, scope, free, (s,(pkd,prk))::scope_ty, free_ty)
       in (TyAbs{Bvar=PT(Vartype v',l), Body=Body', Locn=l}, (lscope, scope, free', scope_ty', free_ty'))
       end

in (* local *)

fun make_aq_ty l ty {scope,free,scope_ty,free_ty} = let
  open Pretype Term Preterm
  val (pty, (_,_,free,_,free_ty)) = from_ty l (destruct_type ty) ([],scope,free,scope_ty,free_ty)
in
  (pty, {scope=scope, free=free, scope_ty=scope_ty, free_ty=free_ty})
end;

fun make_aq l tm {scope,free,scope_ty,free_ty} = let
  open Pretype Term Preterm
  val (ptm, (_,_,free,_,free_ty)) = from l (dest_term tm) ([],scope,free,scope_ty,free_ty)
in
  (ptm, {scope=scope, free=free, scope_ty=scope_ty, free_ty=free_ty})
end

end; (* local *)


(*---------------------------------------------------------------------------*
 * Generating fresh constant instances                                       *
 *---------------------------------------------------------------------------*)

fun gen_thy_const l (thy,s) =
  let val c = Term.prim_mk_const{Name=s, Thy=thy}
  in Preterm.Const {Name=s, Thy=thy, Locn=l,
        Ty=Pretype.rename_typevars
                 (Pretype.fromType (Term.type_of c))}
  end

fun gen_const l s =
 case Term.decls s
  of [] => raise ERRORloc "gen_const" l ("unable to find constant "^Lib.quote s)
   | h::_ => let val {Name,Thy,Ty} = Term.dest_thy_const h
             in Preterm.Const
                  {Name=Name, Thy=Thy, Locn = l,
                   Ty=Pretype.rename_typevars (Pretype.fromType Ty)}
             end



(*---------------------------------------------------------------------------
 * Binding occurrences of variables
 *---------------------------------------------------------------------------*)

fun make_binding_occ l s binder E =
 let open Preterm
     val _ =
       Lexis.ok_identifier s orelse
       Lexis.ok_symbolic s orelse
       raise ERRORloc "make_binding_occ" l
         (s ^ " is not lexically permissible as a binding variable")
     val ntv = Pretype.all_new_uvar()
     val E' = add_scope((s,ntv),E)
 in
  case binder
   of "\\" => ((fn b => Abs{Bvar=Var{Name=s, Ty=ntv, Locn=l},Body=b,Locn=locn.near (Preterm.locn b)}), E')
    |  _   => ((fn b => Comb{Rator=gen_const l binder, Locn=locn.near (Preterm.locn b),
                                  Rand=Abs{Bvar=Var{Name=s,Ty=ntv,Locn=l}, Body=b, Locn=locn.near (Preterm.locn b)}}), E')
 end;

fun make_tybinding_occ l s binder E =
 let open Pretype Preterm
     val _ =
       Lexis.allowed_user_type_var s orelse
       raise ERRORloc "make_binding_occ" l
         (s ^ " is not lexically permissible as a binding type variable")
     val nkv = Prekind.new_uvar()
     val nrv = Prerank.new_uvar()
     val pty = PT(Vartype(s, nkv, nrv), l)
     val E' = add_scope_ty((s, nkv, nrv),E)
 in ((fn b => TyAbs{Bvar=pty, Body=b, Locn=locn.near (Preterm.locn b)}), E')
 end;



fun make_aq_binding_occ l aq binder E = let
  val (v as (Name,Ty)) = Term.dest_var aq
  val pty = Pretype.fromType Ty
  val v' = {Name=Name, Ty=Pretype.fromType Ty, Locn=l}
  val E' = add_scope ((Name,pty),E)
  open Preterm
in
  case binder of
    "\\"   => ((fn b => Abs{Bvar=Var v', Body=b, Locn=locn.near (Preterm.locn b)}), E')
  | binder => ((fn b => Comb{Rator=gen_const l binder, Locn=locn.near (Preterm.locn b),
                             Rand=Abs{Bvar=Var v', Body=b, Locn=locn.near (Preterm.locn b)}}),  E')
end

fun make_binding_type_occ l s binder E =
 let open Pretype
     val _ =
       Lexis.allowed_user_type_var s orelse
       raise ERRORloc "make_binding_type_occ" l
         (s ^ " is not lexically permissible as a binding type variable")
     val nkv = Prekind.new_uvar()
     val nrv = Prerank.new_uvar()
     val pty = PT(Vartype(s, nkv, nrv), l)
     val E' = add_scope_ty((s,nkv,nrv),E)
 in
  case binder
   of "\\" => ((fn b => PT(TyAbst(pty,b), locn.near (tylocn b))), E')
    | "!"  => ((fn b => PT(TyUniv(pty,b), locn.near (tylocn b))), E')
    |  _   => raise ERROR "make_tybinding_occ" ("invalid binder: " ^ binder)
 end;

local open Pretype
in
fun cdomkd M [] = M
  | cdomkd (PT(TyUniv(Bvar,Body),Locn)) (kd::rst) =
       PT(TyUniv(PT(TyKindConstr{Ty=Bvar,Kind=kd},Locn), cdomkd Body rst), Locn)
  | cdomkd (PT(TyAbst(Bvar,Body),Locn)) (kd::rst) =
       PT(TyAbst(PT(TyKindConstr{Ty=Bvar,Kind=kd},Locn), cdomkd Body rst), Locn)
  | cdomkd x y = raise ERRORloc "cdomkd" (Pretype.tylocn x) "missing case"
end;

fun cdomfkd (f,e) kd = ((fn ty => cdomkd (f ty) [kd]), e)

fun make_kind_binding_occ l bty kd binder E = cdomfkd (bty binder E) kd;

local open Pretype
in
fun cdomrk M [] = M
  | cdomrk (PT(TyUniv(Bvar,Body),Locn)) (rk::rst) =
       PT(TyUniv(PT(TyRankConstr{Ty=Bvar,Rank=rk},Locn), cdomrk Body rst), Locn)
  | cdomrk (PT(TyAbst(Bvar,Body),Locn)) (rk::rst) =
       PT(TyAbst(PT(TyRankConstr{Ty=Bvar,Rank=rk},Locn), cdomrk Body rst), Locn)
  | cdomrk x y = raise ERRORloc "cdomrk" (Pretype.tylocn x) "missing case"
end;

fun cdomfrk (f,e) rk = ((fn ty => cdomrk (f ty) [rk]), e)

fun make_rank_binding_occ l bty rk binder E = cdomfrk (bty binder E) rk;

local open Preterm Pretype
in
fun cdomkd2 M [] = M
  | cdomkd2 (TyAbs{Bvar,Body,Locn}) (kd::rst) =
       TyAbs{Bvar=PT(TyKindConstr{Ty=Bvar,Kind=kd},Locn), Body=cdomkd2 Body rst, Locn=Locn}
  | cdomkd2 x y = raise ERRORloc "cdomkd2" (Preterm.locn x) "missing case"
end;

fun cdomfkd2 (f,e) kd = ((fn tm => cdomkd2 (f tm) [kd]), e)

fun make_kind_tybinding_occ l bty kd binder E = cdomfkd2 (bty binder E) kd;

local open Preterm Pretype
in
fun cdomrk2 M [] = M
  | cdomrk2 (TyAbs{Bvar,Body,Locn}) (rk::rst) =
       TyAbs{Bvar=PT(TyRankConstr{Ty=Bvar,Rank=rk},Locn), Body=cdomrk2 Body rst, Locn=Locn}
  | cdomrk2 x y = raise ERRORloc "cdomrk2" (Preterm.locn x) "missing case"
end;

fun cdomfrk2 (f,e) rk = ((fn tm => cdomrk2 (f tm) [rk]), e)

fun make_rank_tybinding_occ l bty rk binder E = cdomfrk2 (bty binder E) rk;


(*---------------------------------------------------------------------------
 * Free occurrences of variables.
 *---------------------------------------------------------------------------*)

fun make_free_var l (s,E) =
 let open Preterm
 in (Var{Name=s, Ty=lookup_fvar(s,E), Locn=l}, E)
     handle HOL_ERR _ =>
       let val tyv = Pretype.all_new_uvar()
       in (Var{Name=s, Ty=tyv, Locn=l}, add_free((s,tyv), E))
       end
 end

fun make_free_tyvar l ((s,kd,rk),E) =
 let open Pretype
 in let val (kd, rk) = lookup_ftyvar(s,E)
    in (PT(Vartype(s, kd, rk), l), E)
    end
     handle HOL_ERR _ =>
       let (*val kdv = Prekind.new_uvar()
             val rkv = Prerank.new_uvar()*)
           val v = (s, kd, rk)
       in (PT(Vartype v, l), add_free_ty(v, E))
       end
 end

(*---------------------------------------------------------------------------
 * Bound occurrences of variables.
 *---------------------------------------------------------------------------*)

fun make_bvar l (s,E) = (Preterm.Var{Name=s, Ty=lookup_bvar(s,E), Locn=l}, E);

fun make_btyvar l (s,E) =
    let open Pretype
        val (kind,rank) = lookup_btyvar(s,E)
(*
        val _ = print (">> looking up bound type variable \""^s^"\": found "^
                       "kind="^Kind.kind_to_string (Prekind.toKind kind)^
                       ", rank="^Int.toString (Prerank.toRank rank)^"\n")
*)
    in (PT(Vartype(s,kind,rank), l), E)
    end;

(* ----------------------------------------------------------------------
     Treatment of overloaded identifiers
 ---------------------------------------------------------------------- *)

fun gen_overloaded_const oinfo l s =
 let open Overload
     val opinfo = valOf (info_for_name oinfo s)
         handle Option => raise Fail "gen_overloaded_const: invariant failure"
 in
  case #actual_ops opinfo
   of [{Ty,Name,Thy}] =>
         Preterm.Const{Name=Name, Thy=Thy, Locn=l,
                   Ty=Pretype.rename_typevars (Pretype.fromType Ty)}
  | otherwise =>
     let val base_pretype0 = Pretype.fromType (#base_type opinfo)
         val new_pretype = Pretype.rename_typevars base_pretype0
     in Preterm.Overloaded{Name = s, Ty = new_pretype, Info = opinfo, Locn = l}
    end
 end


(*---------------------------------------------------------------------------
 * Identifiers work as follows: look for the string in the scope;
 * if it's there, put the bound var.
 * Failing that, check to see if the string is a known constant.
 *
 * If so, it will have an "overloading" entry.  Look this up and proceed.
 *
 * If not, it might be trying to be a record selection; these are
 * necessarily constants (and overloaded) so we can complain at this point.
 *
 * Otherwise, it might be a string literal.  Try and make one, if this
 * fails because stringTheory is not loaded, fail.
 *
 * If none of the above, then it's a free variable.
 *
 * Free vars are placed in the "free" part of the environment; this is a
 * set. Bound vars are placed at the front of the "scope". When we come out
 * of an Abs, we return the scope in effect when entering the Abs, but the
 * "free"s include new ones found in the body of the Abs.
 *---------------------------------------------------------------------------*)

fun make_const l s E = (gen_const l s, E)

(*---------------------------------------------------------------------------
    Making preterm string literals.
 ---------------------------------------------------------------------------*)

local
  fun mk_chr ctm tm = mk_comb(ctm, tm)
  fun mk_string stm (tm1,tm2) = list_mk_comb(stm, [tm1, tm2])
  fun mk_numeral n =
      Literal.gen_mk_numeral
        {mk_comb = mk_comb,
         ZERO = prim_mk_const{Name = "0", Thy = "num"},
         ALT_ZERO = prim_mk_const{Name = "ZERO", Thy = "arithmetic"},
         NUMERAL = prim_mk_const {Name="NUMERAL",Thy="arithmetic"},
         BIT1 = prim_mk_const {Name="BIT1", Thy="arithmetic"},
         BIT2 = prim_mk_const {Name="BIT2", Thy="arithmetic"}} n
  fun fromMLC ctm c = mk_chr ctm (mk_numeral (Arbnum.fromInt (Char.ord c)))
in
fun make_string_literal l s =
    if not (mem "string" (ancestry "-")) andalso
       current_theory() <> "string"
    then
      Raise (ERRORloc "make_string_literal" l
                      ("String literals not allowed - "^
                       "load \"stringTheory\" first."))
    else let
        val stm = prim_mk_const {Name = "STRING", Thy = "string"}
        val ctm = prim_mk_const {Name = "CHR", Thy = "string"}
        val etm = prim_mk_const{Name = "EMPTYSTRING", Thy = "string"}
      in
        Preterm.Antiq {Locn = l,
                       Tm = Literal.mk_string_lit
                              {mk_string = mk_string stm,
                               emptystring = etm,
                               fromMLchar = fromMLC ctm}
                              (String.substring(s,1,String.size s - 2))}
      end
fun make_char_literal l s =
    if not (mem "string" (ancestry "-")) andalso
       current_theory() <> "string"
    then
      raise (ERRORloc "make_char_literal" l
                      "Char literals not allowed - \
                      \load \"stringTheory\" first.")
    else let
        val ctm = prim_mk_const {Name = "CHR", Thy = "string"}
        val n_t = mk_numeral (Arbnum.fromInt (Char.ord (String.sub(s,2))))
      in
        Preterm.Antiq{Locn = l, Tm = mk_chr ctm n_t}
      end
end (* local *)

(*---------------------------------------------------------------------------
    "make_qconst" ignores overloading and visibility information. The
    idea is that if we ask to make a long identifier, it should be
    treated as visible.
 ---------------------------------------------------------------------------*)

fun make_qconst _ l (p as (thy,s)) E = (gen_thy_const l p, E);

fun make_atom oinfo l s E =
 make_bvar l (s,E) handle HOL_ERR _
  =>
  if Overload.is_overloaded oinfo s then
    (gen_overloaded_const oinfo l s, E)
  else
  case List.find (fn rfn => String.isPrefix rfn s)
                 [recsel_special, recupd_special, recfupd_special]
   of NONE => if Lexis.is_string_literal s then (make_string_literal l s, E)
              else if Lexis.is_char_literal s then (make_char_literal l s, E)
              else make_free_var l (s, E)
    | SOME rfn =>
        Raise (ERRORloc "make_atom" l
                     ("Record field "^String.extract(s, size rfn, NONE)^
                      " not registered"))

fun make_type_constant l {Thy=Thy0,Tyop=Tyop0} E =
 let open Pretype
     val c = Type.mk_thy_con_type {Thy=Thy0,Tyop=Tyop0}
     val {Thy,Tyop,Kind,Rank} = Type.dest_thy_con_type c
     val Kind' = Prekind.fromKind Kind
     val Rank' = Prerank.fromRank Rank
 in (PT(Contype {Thy=Thy,Tyop=Tyop,Kind=Kind',Rank=Rank'}, l), E)
 end

fun make_type_atom l (s,kd,rk) E =
 make_btyvar l (s,E)
   handle HOL_ERR _ =>
   make_free_tyvar l ((s,kd,rk), E)

fun make_uvar_type l r NONE E =
    (Pretype.PT(Pretype.UVar r, l), E)
  | make_uvar_type l r (SOME ty) E =
    let val (ty', E') = ty E
    in
      r := SOMEU ty';
      (Pretype.PT(Pretype.UVar r, l), E')
    end;

(*---------------------------------------------------------------------------
 * Combs
 *---------------------------------------------------------------------------*)

fun list_make_comb l (tm1::(rst as (_::_))) E =
     rev_itlist (fn tm => fn (trm,e) =>
        let val (tm',e') = tm e
        in (Preterm.Comb{Rator = trm, Rand = tm', Locn=l}, e') end)     rst (tm1 E)
  | list_make_comb l _ _ = raise ERRORloc "list_make_comb" l "insufficient args";

fun list_make_tycomb l tm1 (tys as (_::_)) E =
     rev_itlist (fn ty => fn (trm,e) =>
        let val (ty',e') = ty e
        in (Preterm.TyComb{Rator = trm, Rand = ty', Locn=l}, e') end)   tys (tm1 E)
  | list_make_tycomb l _ _ _ = raise ERRORloc "list_make_tycomb" l "insufficient args";

fun list_make_app_type l (ty1::(rst as (_::_))) E =
     rev_itlist (fn ty => fn (typ,e) =>
        let val (ty',e') = ty e
        in (Pretype.PT(Pretype.TyApp(typ, ty'), l), e') end)     rst (ty1 E)
  | list_make_app_type l _ _ = raise ERRORloc "list_make_app_type" l "insufficient args";

(*---------------------------------------------------------------------------
 * Constraints
 *---------------------------------------------------------------------------*)

fun make_constrained l tm ty E = let
  val (tm',E') = tm E
  val (ty',E'') = ty E'
in
  (Preterm.Constrained{Ptm = tm', Ty = ty', Locn = l}, E'')
end;

fun make_kind_constr_type l ty kd E = let
  val (ty',E') = ty E
  open Pretype
in
  (PT(TyKindConstr{Ty = ty', Kind = kd}, l), E')
end;

fun make_rank_constr_type l ty rk E = let
  val (ty',E') = ty E
  open Pretype
in
  (PT(TyRankConstr{Ty = ty', Rank = rk}, l), E')
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

fun bind_term _ binder alist tm (E as {scope=scope0,scope_ty=scope_ty0,...}:env) =
   let val (E',F) = rev_itlist (fn a => fn (e,f) =>
             let val (g,e') = a binder e in (e', f o g) end) alist (E,I)
       val (tm',({free=free1,free_ty=free_ty1,...}:env)) = tm E'
   in (F tm', {scope=scope0,free=free1,scope_ty=scope_ty0,free_ty=free_ty1})
   end;

fun tybind_term _ binder alist tm (E as {scope=scope0,scope_ty=scope_ty0,...}:env) =
   let val (E',F) = rev_itlist (fn a => fn (e,f) =>
             let val (g,e') = a binder e in (e', f o g) end) alist (E,I)
       val (tm',({free=free1,free_ty=free_ty1,...}:env)) = tm E'
   in (F tm', {scope=scope0,free=free1,scope_ty=scope_ty0,free_ty=free_ty1})
   end;

fun bind_type _ binder alist ty (E as {scope=scope0,scope_ty=scope_ty0,...}:env) =
   let val (E',F) = rev_itlist (fn a => fn (e,f) =>
             let val (g,e') = a binder e in (e', f o g) end) alist (E,I)
       val (ty',({free=free1,free_ty=free_ty1,...}:env)) = ty E'
   in (F ty', {scope=scope0,free=free1,scope_ty=scope_ty0,free_ty=free_ty1})
   end;


(*---------------------------------------------------------------------------
 * For restricted binders. Adding a pair "(B,R)" to this list, if "B" is the
 * name of a binder and "R" is the name of a constant, will enable parsing
 * of terms with the form
 *
 *     B <varstruct list>::<restr>. M
 *---------------------------------------------------------------------------*)

local val restricted_binders = ref ([] : (string * string) list)
in
fun binder_restrictions() = !restricted_binders
fun associate_restriction l (p as (binder_str,const_name)) =
  case (Lib.assoc1 binder_str (!restricted_binders)) of
    NONE => restricted_binders := p :: !restricted_binders
  | SOME _ =>
      raise ERRORloc "restrict_binder" l
        ("Binder "^Lib.quote binder_str^" is already restricted")

fun delete_restriction l binder =
 restricted_binders :=
  Lib.set_diff (!restricted_binders)
         [(binder,Lib.assoc binder(!restricted_binders))]
  handle HOL_ERR _
   => raise ERRORloc "delete_restriction" l (Lib.quote binder^" is not restricted")
end;

fun restr_binder l s =
   assoc s (binder_restrictions()) handle HOL_ERR _
   => raise ERRORloc "restr_binder" l
                      ("no restriction associated with "^Lib.quote s)

fun bind_restr_term l binder vlist restr tm (E as {scope=scope0,scope_ty=scope_ty0,...}:env)=
   let fun replicate_rbinder e =
            (gen_const l (restr_binder l binder),e)
             handle HOL_ERR _ => raise ERRORloc "bind_restr_term" l
              ("Can't find constant associated with "^Lib.quote binder)
       val (E',F) =
          rev_itlist (fn v => fn (e,f)
             => let val (prefix,e') = list_make_comb l [replicate_rbinder,restr] e
                    val (g,e'') = v "\\" e'
                    fun make_cmb ptm = Preterm.Comb{Rator=prefix,Rand=ptm,Locn=l}
                in (e'', f o make_cmb o g) end)         vlist (E,I)
       val (tm',({free=free1,free_ty=free_ty1,...}:env)) = tm E'
   in
   (F tm', {scope=scope0,scope_ty=scope_ty0,free=free1,free_ty=free_ty1})
   end;

fun split (Pretype.PT(ty,locn)) = let
  open Pretype
  val pair_conty = Contype{Thy = "pair", Tyop = "prod",
                           Kind = Prekind.mk_arity 2, Rank = Prerank.Zerorank}
in
  case ty of
    TyApp(PT(TyApp(PT(con, _), arg1), _), arg2) => if con = pair_conty then
                                                     [arg1, arg2]
                                                   else
                                                     raise ERROR "split" "not a prod"
  | _ => raise ERROR "split" "not a product"
end


local open Preterm
in
fun cdom M [] = M
  | cdom (Abs{Bvar,Body,Locn}) (ty::rst) =
       Abs{Bvar = Constrained{Ptm=Bvar,Ty=ty,Locn=Locn}, Body = cdom Body rst, Locn = Locn}
  | cdom (Comb{Rator as Const{Name="UNCURRY",...},Rand,Locn}) (ty::rst) =
       Comb{Rator=Rator, Rand=cdom Rand (split ty@rst), Locn=Locn}
  | cdom x y = raise ERRORloc "cdom" (Preterm.locn x) "missing case"
end;

fun cdomf (f,e) ty = ((fn tm => cdom (f tm) [ty]), e)

fun make_vstruct l bvl tyo binder E = let
  open Preterm
  fun loop ([v],E) = v "\\" E
    | loop ((v::rst),E) = let
        val (f,e) = v "\\" E
        val (F,E') = loop(rst,e)
      in
        ((fn b => Comb{Rator=gen_const l "UNCURRY",Rand=f(F b),Locn=l}), E')
      end
    | loop _ = raise ERRORloc "make_vstruct" l "impl. error, empty vstruct"
  val (F,E') =
    case tyo of
      NONE    => loop(bvl,E)
    | SOME ty => let val (ty',E') = ty E
                 in cdomf (hd bvl "\\" E') ty'
                 end
in
  case binder of
    "\\" => (F,E')
  | _ => ((fn b => Comb{Rator=gen_const l binder,Rand=F b,Locn=l}), E')
end;


(*---------------------------------------------------------------------------
 * Let bindings
 *---------------------------------------------------------------------------*)
fun make_let l bindings tm env =
   let open Preterm
       val {body_bvars, args, E} =
          itlist (fn (bvs,arg) => fn {body_bvars,args,E} =>
                    let val (b,rst) = (hd bvs,tl bvs)
                        val (arg',E') =
                          case rst of [] => arg E | L => bind_term l "\\" L arg E
                    in {body_bvars = b::body_bvars, args=arg'::args, E=E'}
                    end) bindings {body_bvars=[], args=[], E=env}
       val (core,E') = bind_term l "\\" body_bvars tm E
   in
     ( rev_itlist (fn arg => fn core =>
            Comb{Rator=Comb{Rator=gen_const l "LET",Rand=core,Locn=l},Rand=arg,Locn=l})
           args core, E')
   end
   handle HOL_ERR _ => raise ERRORloc "make_let" l "bad let structure";

fun make_set_const l fname s E =
 (gen_const l s, E)
  handle HOL_ERR _
    => raise ERRORloc fname l ("The theory "^Lib.quote "pred_set"^" is not loaded");


(*---------------------------------------------------------------------------
 * Set abstractions {tm1 | tm2}. The complicated rigamarole at the front is
 * so that new type variables only get made once per free var, although we
 * compute the free vars for tm1 and tm2 separately.
 *
 * You can't make a set unless the theory of sets is an ancestor.
 * The calls to make_set_const ensure this.
 *
 * Warning: apt not to work if you want to "antiquote in" free variables that
 * will subsequently get bound in the set abstraction.
 *---------------------------------------------------------------------------*)

fun make_set_abs l (tm1,tm2) (E as {scope=scope0,...}:env) =
   let val (_,(e1:env)) = tm1 empty_env
       val (_,(e2:env)) = tm2 empty_env
       val (_,(e3:env)) = tm2 e1
       val tm1_fv_names = map fst (#free e1)
       val tm2_fv_names = map fst (#free e2)
       val fv_names = if null tm1_fv_names then tm2_fv_names else
                      if null tm2_fv_names then tm1_fv_names else
                      intersect tm1_fv_names tm2_fv_names
       val init_fv = #free e3
   in
   case gather (fn (name,_) => mem name fv_names) init_fv
     of [] => raise ERRORloc "make_set_abs" l "no free variables in set abstraction"
      | quants =>
         let val quants' = map
                (fn (bnd as (Name,Ty)) =>
                     (fn (s:string) => fn E =>
                       ((fn b => Preterm.Abs{Bvar=Preterm.Var{Name=Name,Ty=Ty,Locn=l(*ugh*)},
                                             Body=b, Locn=l}),
                                add_scope(bnd,E))))
               (rev quants) (* make_vstruct expects reverse occ. order *)
         in list_make_comb l
               [(make_set_const l "make_set_abs" "GSPEC"),
                (bind_term l "\\" [make_vstruct l quants' NONE]
                          (list_make_comb l [make_const l ",",tm1,tm2]))] E
         end
   end;

(*---------------------------------------------------------------------------
 * Sequence abstractions [| tm1 | tm2 |].
 *
 * You can't make a llist unless llistTheory is an ancestor.
 * The call to make_seq_comp_const ensure this.
 *---------------------------------------------------------------------------*)
(*
fun make_seqComp_const l fname s E =
 (gen_const l s, E)
  handle HOL_ERR _
    => raise ERRORloc fname l ("The theory "^Lib.quote "llist"^" is not loaded");

fun make_seq_abs l (tm1,tm2) (E as {scope=scope0,...}:env) =
   let val (_,(e1:env)) = tm1 empty_env
       val (_,(e2:env)) = tm2 empty_env
       val (_,(e3:env)) = tm2 e1
       val tm1_fv_names = map fst (#free e1)
       val tm2_fv_names = map fst (#free e2)
       val fv_names = if null tm1_fv_names then tm2_fv_names else
                      if null tm2_fv_names then tm1_fv_names else
                      intersect tm1_fv_names tm2_fv_names
       val init_fv = #free e3
   in
   case gather (fn (name,_) => mem name fv_names) init_fv
     of [] => raise ERRORloc "make_seq_abs" l "no free variables in set abstraction"
      | quants =>
         let val quants' = map
                (fn (bnd as (Name,Ty)) =>
                     (fn (s:string) => fn E =>
                       ((fn b => Preterm.Abs{Bvar=Preterm.Var{Name=Name,Ty=Ty,Locn=l(*ugh*)},
                                             Body=b, Locn=l}),
                                add_scope(bnd,E))))
               (rev quants) (* make_vstruct expects reverse occ. order *)
         in list_make_comb l
               [(make_seqComp_const l "make_seq_abs" "SeqComp"),
                (bind_term l "\\" [make_vstruct l quants' NONE]
                          (list_make_comb l [make_const l ",",tm1,tm2]))] E
         end
   end;
*)

end; (* Parse_support *)
