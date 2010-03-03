structure Pretype :> Pretype =
struct

open HolKernel optmonad;
infix >> >-;
infixr ==>;

  type prekind = Prekind.prekind
  type prerank = Prerank.prerank
  type oprerank = Prerank.oprerank
  type kind = Kind.kind
  type hol_type = Type.hol_type
  type pretyvar = string * prekind * prerank
  type tyvar = Type.tyvar

val debug = ref 0
val _ = Feedback.register_trace("debug_pretype", debug, 1)
fun is_debug() = (!debug) > 0;

val beta_conv_types = ref 1
val _ = Feedback.register_trace("beta_conv_types", beta_conv_types, 1)
fun do_beta_conv_types() = (!beta_conv_types) > 0;

val TCERR = mk_HOL_ERR "Pretype";
val ERRloc = mk_HOL_ERRloc "Pretype"

fun kcheck_say s = if Feedback.current_trace "show_typecheck_errors" > 0 handle _ => true
                   then Lib.say s else ()

datatype kcheck_error =
         TyAppFail of hol_type * hol_type
       | TyUnivFail of hol_type
       | TyKindConstrFail of hol_type * kind
       | TyRankConstrFail of hol_type * int
       | TyRankLEConstrFail of hol_type * int

val last_kcerror : (kcheck_error * locn.locn) option ref = ref NONE

 datatype pretype0
    = Vartype of pretyvar
    | Contype of {Thy : string, Tyop : string, Kind : prekind, Rank : prerank}
    | TyApp  of pretype * pretype
    | TyUniv of pretype * pretype
    | TyAbst of pretype * pretype
    | TyKindConstr of {Ty : pretype, Kind : prekind}
    | TyRankConstr of {Ty : pretype, Rank : prerank}
    | UVar of uvartype ref
 and uvartype
    = SOMEU of pretype
    | NONEU of prekind * prerank
 and pretype = PT of pretype0 locn.located

fun isSomeU (SOMEU _) = true
  | isSomeU (NONEU _) = false

fun THEU (SOMEU v) = v
  | THEU (NONEU _) = raise TCERR "THEU" "uvartype not a SOMEU";

fun tylocn (PT(_,locn)) = locn

(*---------------------------------------------------------------------------
  Location-ignoring but alpha-equivalence respecting equality for pretypes.
 ---------------------------------------------------------------------------*)

val eq_kind = Prekind.eq
val eq_rank = Prerank.eq

fun eq_tyvar (s,kd,rk) (s',kd',rk') = s=s' (*andalso eq_kind kd kd' andalso eq_rank rk rk'*)

fun Vartype_of0 (Vartype v) = v
  | Vartype_of0 (TyKindConstr{Ty, Kind}) =
       let val (s,kd,rk) = Vartype_of Ty in (s,Kind,rk) end
  | Vartype_of0 (TyRankConstr{Ty, Rank}) =
       let val (s,kd,rk) = Vartype_of Ty in (s,kd,Rank) end
  | Vartype_of0 _ = raise TCERR "Vartype_of" "not a variable or a kind or rank constraint"
and Vartype_of (PT(ty,locn)) = Vartype_of0 ty;

fun eq_varty   []      []    v v' = eq_tyvar v v'
  | eq_varty (x::xs) (y::ys) v v' =
      let val x_eq_v = eq_tyvar x v and y_eq_v' = eq_tyvar y v'
      in (x_eq_v andalso y_eq_v') orelse
         (not x_eq_v andalso not y_eq_v' andalso eq_varty xs ys v v')
      end
  | eq_varty   _       _     _ _  = false

fun eq_env0 e1 e2 (Vartype v)                (Vartype v')              = eq_varty e1 e2 v v'
  | eq_env0 e1 e2 (Contype{Tyop=Tyop, Thy=Thy, Kind=Kind, Rank=Rank })
                  (Contype{Tyop=Tyop',Thy=Thy',Kind=Kind',Rank=Rank'}) = Tyop=Tyop' andalso Thy=Thy'
                                                         andalso eq_kind Kind Kind' andalso eq_rank Rank Rank'
  | eq_env0 e1 e2 (TyApp(ty1,ty2))           (TyApp(ty1',ty2'))        = eq_env e1 e2 ty1 ty1' andalso eq_env e1 e2 ty2 ty2'
  | eq_env0 e1 e2 (TyUniv(ty1,ty2))          (TyUniv(ty1',ty2'))       =
          eq_env (Vartype_of ty1::e1) (Vartype_of ty1'::e2) ty2 ty2'
  | eq_env0 e1 e2 (TyAbst(ty1,ty2))          (TyAbst(ty1',ty2'))       =
          eq_env (Vartype_of ty1::e1) (Vartype_of ty1'::e2) ty2 ty2'
  | eq_env0 e1 e2 (TyKindConstr{Ty=ty, Kind=kd })
                  (TyKindConstr{Ty=ty',Kind=kd'})                      = eq_env e1 e2 ty ty' andalso eq_kind kd kd'
  | eq_env0 e1 e2 (TyRankConstr{Ty=ty, Rank=rk })
                  (TyRankConstr{Ty=ty',Rank=rk'})                      = eq_env e1 e2 ty ty' andalso eq_rank rk rk'
  | eq_env0 e1 e2 (UVar (r  as ref (NONEU(kd, rk ))))
                  (UVar (r' as ref (NONEU(kd',rk'))))                  = r=r'
  | eq_env0 e1 e2 (UVar (ref (SOMEU ty)))    (UVar (ref (SOMEU ty')))  = eq_env e1 e2 ty ty'
  | eq_env0 e1 e2 (UVar (ref (SOMEU ty)))    ty'                       = eq_env e1 e2 ty (PT(ty',locn.Loc_None))
  | eq_env0 e1 e2 ty                         (UVar (ref (SOMEU ty')))  = eq_env e1 e2 (PT(ty,locn.Loc_None)) ty'
  | eq_env0 e1 e2 _                          _                         = false
and eq_env  e1 e2 (PT (value,locn))          (PT (value',locn'))       = eq_env0 e1 e2 value value'

val eq0 = eq_env0 [] []
and eq  = eq_env  [] [];

fun list_eq (e1::es1) (e2::es2) = eq e1 e2 andalso list_eq es1 es2
  | list_eq [] [] = true
  | list_eq _ _ = false;

val prekind_rank_compare = Lib.pair_compare(Prekind.prekind_compare, Prerank.prerank_compare);

fun pretyvar_compare ((s1,k1,rk1), (s2,k2,rk2)) =
       (case String.compare (s1,s2)
         of EQUAL => prekind_rank_compare ((k1,rk1),(k2,rk2))
          | x => x)

fun pretype_var_compare (Vartype u, Vartype v) = pretyvar_compare (u,v)
  | pretype_var_compare _ = raise ERR "pretype_var_compare" "variables required";

fun pretype_con_compare (Contype{Tyop=Tyop1, Thy=Thy1, Kind=Kind1, Rank=Rank1},
                         Contype{Tyop=Tyop2, Thy=Thy2, Kind=Kind2, Rank=Rank2}) =
       (case Lib.pair_compare(String.compare,String.compare)((Thy1,Tyop1),(Thy2,Tyop2))
         of EQUAL => prekind_rank_compare ((Kind1,Rank1),(Kind2,Rank2))
          | x => x)
  | pretype_con_compare _ =raise ERR "pretype_con_compare" "constants required";

(* ----------------------------------------------------------------------
    A total ordering on pretypes that does not respect alpha equivalence.
       It does ignore locations.
    Vartype < Contype < TyApp < TyUniv < TyAbst < TyKindConstr < TyRankConstr
            < UVar(NONE) < UVar(SOME)
   ---------------------------------------------------------------------- *)

fun compare (p as (PT(ty1,_),PT(ty2,_))) =
    if Portable.pointer_eq p then EQUAL else compare0 (ty1,ty2)
and compare0 (ty1,ty2) =
    case (ty1,ty2) of
      (u as Vartype _, v as Vartype _)   => pretype_var_compare (u,v)
    | (Vartype _, _)                     => LESS
    | (Contype _, Vartype _)             => GREATER
    | (u as Contype _, v as Contype _)   => pretype_con_compare (u,v)
    | (Contype _, _)                     => LESS
    | (TyApp _, Vartype _)               => GREATER
    | (TyApp _, Contype _)               => GREATER
    | (TyApp p1, TyApp p2)               => Lib.pair_compare(compare,compare)(p1,p2)
    | (TyApp _, _)                       => LESS
    | (TyUniv _, Vartype _)              => GREATER
    | (TyUniv _, Contype _)              => GREATER
    | (TyUniv _, TyApp _)                => GREATER
    | (TyUniv(bv1,ty1), TyUniv(bv2,ty2)) =>
                            Lib.pair_compare(compare,compare) ((bv1,ty1),(bv2,ty2))
    | (TyUniv _, _)                      => LESS
    | (TyAbst _, Vartype _)              => GREATER
    | (TyAbst _, Contype _)              => GREATER
    | (TyAbst _, TyApp _)                => GREATER
    | (TyAbst _, TyUniv _)               => GREATER
    | (TyAbst(bv1,ty1), TyAbst(bv2,ty2)) =>
                            Lib.pair_compare(compare,compare) ((bv1,ty1),(bv2,ty2))
    | (TyAbst _, _)                      => LESS
    | (TyKindConstr _, UVar _)           => LESS
    | (TyKindConstr _, TyRankConstr _)   => LESS
    | (TyKindConstr {Ty=ty1,Kind=kd1}, TyKindConstr {Ty=ty2,Kind=kd2}) =>
                            Lib.pair_compare(compare,Prekind.prekind_compare)
                                            ((ty1,kd1),(ty2,kd2))
    | (TyKindConstr _, _)                => GREATER
    | (TyRankConstr _, UVar _)           => LESS
    | (TyRankConstr {Ty=ty1,Rank=rk1}, TyRankConstr {Ty=ty2,Rank=rk2}) =>
                            Lib.pair_compare(compare,Prerank.prerank_compare)
                                            ((ty1,rk1),(ty2,rk2))
    | (TyRankConstr _, _)                => GREATER
    | (UVar (ref(NONEU _)), UVar (ref(SOMEU _))) => LESS
    | (UVar (ref(NONEU(k1,rk1))), UVar (ref(NONEU(k2,rk2)))) => prekind_rank_compare ((k1,rk1),(k2,rk2))
    | (UVar (ref(NONEU _)), _)               => GREATER
    | (UVar (ref(SOMEU ty1)), UVar (ref(SOMEU ty2))) => compare(ty1,ty2)
    | (UVar (ref(SOMEU _)), _)           => GREATER
;


fun ((ty1 as PT(_,loc1)) --> (ty2 as PT(_,loc2))) =
    PT(TyApp(PT(TyApp(PT(Contype {Thy = "min", Tyop = "fun",
                                  Kind = Prekind.mk_arity 2, Rank = Prerank.Zerorank},
                         locn.Loc_None),
                      ty1),
                locn.Loc_None),
             ty2),
       locn.between loc1 loc2)

fun is_var_type(PT(Vartype v,loc)) = true
  | is_var_type _ = false

fun is_uvar_type(PT(UVar r,loc)) = true
  | is_uvar_type _ = false

fun has_var_type(ty as PT(Vartype v,loc)) = true
  | has_var_type(PT(TyKindConstr{Ty,Kind},loc)) = has_var_type Ty
  | has_var_type(PT(TyRankConstr{Ty,Rank},loc)) = has_var_type Ty
  | has_var_type(PT(UVar(ref(SOMEU ty)),loc))   = has_var_type ty
  | has_var_type(ty as PT(UVar(ref(NONEU _)),loc)) = true
  | has_var_type _ = false;

fun dest_var_type(PT(Vartype v,loc)) = v
  | dest_var_type(PT(UVar(ref(SOMEU ty)),loc)) = dest_var_type ty
  | dest_var_type _ = raise TCERR "dest_var_type" "not a type variable";

local
fun rstrip_app_type(PT(TyApp(ty1,ty2), _)) = let val (opr,args) = rstrip_app_type ty1
                                             in (opr, ty2::args)
                                             end
  | rstrip_app_type(PT(TyKindConstr{Ty,Kind},loc)) = rstrip_app_type Ty
  | rstrip_app_type(PT(TyRankConstr{Ty,Rank},loc)) = rstrip_app_type Ty
  | rstrip_app_type(PT(UVar(ref(SOMEU ty)),loc))   = rstrip_app_type ty
  | rstrip_app_type ty = (ty,[])
in
fun strip_app_type ty = let val (opr,args) = rstrip_app_type ty
                        in (opr, rev args)
                        end
end;

fun the_var_type(ty as PT(Vartype v,loc)) = ty
  | the_var_type(PT(TyKindConstr{Ty,Kind},loc)) = the_var_type Ty
  | the_var_type(PT(TyRankConstr{Ty,Rank},loc)) = the_var_type Ty
  | the_var_type(PT(UVar(ref(SOMEU ty)),loc))   = the_var_type ty
  | the_var_type(ty as PT(UVar(ref(NONEU _)),loc)) = ty
  | the_var_type _ = raise TCERR "the_var_type" "not a type variable";

fun the_con_type(ty as PT(Contype v,loc)) = ty
  | the_con_type(PT(TyKindConstr{Ty,Kind},loc)) = the_con_type Ty
  | the_con_type(PT(TyRankConstr{Ty,Rank},loc)) = the_con_type Ty
  | the_con_type(PT(UVar(ref(SOMEU ty)),loc))   = the_con_type ty
  | the_con_type _ = raise TCERR "the_con_type" "not a type constant";

fun dest_con_type(PT(Contype v,loc)) = v
  | dest_con_type(PT(TyKindConstr{Ty,Kind},loc)) = dest_con_type Ty
  | dest_con_type(PT(TyRankConstr{Ty,Rank},loc)) = dest_con_type Ty
  | dest_con_type(PT(UVar(ref(SOMEU ty)),loc))   = dest_con_type ty
  | dest_con_type _ = raise TCERR "dest_con_type" "not a type constant";

fun mk_app_type(ty1 as PT(_,loc1), ty2 as PT(_,loc2)) =
    PT(TyApp(ty1,ty2), locn.between loc1 loc2)

fun list_mk_app_type(tyop, ty::tys) = list_mk_app_type(mk_app_type(tyop, ty), tys)
  | list_mk_app_type(tyop,   []   ) = tyop

fun dest_app_type(PT(UVar(ref(SOMEU ty))  ,loc)) = dest_app_type ty
  | dest_app_type(PT(TyKindConstr{Ty,Kind},loc)) = dest_app_type Ty
  | dest_app_type(PT(TyRankConstr{Ty,Rank},loc)) = dest_app_type Ty
  | dest_app_type(PT(TyApp(ty1,ty2)       ,loc)) = (ty1,ty2)
  | dest_app_type _ = raise TCERR "dest_app_type" "not a type application";

val is_app_type = can dest_app_type

fun mk_univ_type(ty1 as PT(_,loc1), ty2 as PT(_,loc2)) =
    PT(TyUniv(ty1,ty2), locn.between loc1 loc2)

(* dest_univ_type is defined below after the definition of beta conversion. *)
fun dest_univ_type0(PT(UVar(ref(SOMEU ty)),loc)) = dest_univ_type0 ty
  | dest_univ_type0(PT(TyKindConstr{Ty,Kind},loc)) = dest_univ_type0 Ty
  | dest_univ_type0(PT(TyRankConstr{Ty,Rank},loc)) = dest_univ_type0 Ty
  | dest_univ_type0(ty as PT(TyUniv(ty1,ty2),loc)) = (ty1,ty2)
  | dest_univ_type0 _ = raise TCERR "dest_univ_type" "not a universal type";

val is_univ_type = can dest_univ_type0

(* is_not_abs_type is true iff the argument is decidedly NOT a type abstraction. *)
(* Such a type would clash if unified with an abstraction type. *)
fun is_not_abs_type(PT(UVar(ref(SOMEU ty)),loc)) = is_not_abs_type ty
  | is_not_abs_type(PT(UVar(ref(NONEU _ )),loc)) = false
  | is_not_abs_type(PT(TyKindConstr{Ty,Kind},loc)) = is_not_abs_type Ty
  | is_not_abs_type(PT(TyRankConstr{Ty,Rank},loc)) = is_not_abs_type Ty
  | is_not_abs_type(PT(TyAbst(ty1,ty2),loc)) = false
  | is_not_abs_type(PT(TyApp(ty1,ty2),loc)) = is_not_abs_type ty1
  | is_not_abs_type _ = true;

(* is_not_univ_type is true iff the argument is decidedly NOT a universal type. *)
(* Such a type would clash if unified with a universal type. *)
fun is_not_univ_type0(PT(UVar(ref(SOMEU ty)),loc)) = is_not_univ_type0 ty
  | is_not_univ_type0(PT(UVar(ref(NONEU _ )),loc)) = false
  | is_not_univ_type0(PT(TyKindConstr{Ty,Kind},loc)) = is_not_univ_type0 Ty
  | is_not_univ_type0(PT(TyRankConstr{Ty,Rank},loc)) = is_not_univ_type0 Ty
  | is_not_univ_type0(PT(TyUniv(ty1,ty2),loc)) = false
  | is_not_univ_type0(PT(TyApp(ty1,ty2),loc)) = is_not_abs_type ty1
  | is_not_univ_type0 _ = true;

(* is_universal is true iff the argument contains a universal type. *)
fun is_universal(PT(UVar(ref(SOMEU ty)),loc)) = is_universal ty
  | is_universal(PT(UVar(ref(NONEU _ )),loc)) = false
  | is_universal(PT(TyKindConstr{Ty,Kind},loc)) = is_universal Ty
  | is_universal(PT(TyRankConstr{Ty,Rank},loc)) = is_universal Ty
  | is_universal(PT(TyUniv(ty1,ty2),loc)) = true
  | is_universal(PT(TyAbst(ty1,ty2),loc)) = is_universal ty2
  | is_universal(PT(TyApp(ty1,ty2),loc)) = is_universal ty1 orelse is_universal ty2
  | is_universal _ = false;

fun mk_abs_type(ty1 as PT(_,loc1), ty2 as PT(_,loc2)) =
    PT(TyAbst(ty1,ty2), locn.between loc1 loc2)

fun list_mk_abs_type([],ty) = ty
  | list_mk_abs_type(v::vs,ty) = mk_abs_type(v,list_mk_abs_type(vs,ty))

fun dest_abs_type(PT(UVar(ref(SOMEU ty)),loc)) = dest_abs_type ty
  | dest_abs_type(ty as PT(TyAbst(ty1,ty2),loc)) = (ty1,ty2)
  | dest_abs_type _ = raise TCERR "dest_abs_type" "not a type abstraction";

fun is_abs_type(PT(UVar(ref(SOMEU ty))  ,loc)) = is_abs_type ty
  | is_abs_type(PT(TyKindConstr{Ty,Kind},loc)) = is_abs_type Ty
  | is_abs_type(PT(TyRankConstr{Ty,Rank},loc)) = is_abs_type Ty
  | is_abs_type(ty as PT(TyAbst(ty1,ty2),loc)) = true
  | is_abs_type _ = false;

fun the_abs_type(PT(UVar(ref(SOMEU ty))  ,loc)) = the_abs_type ty
  | the_abs_type(PT(TyKindConstr{Ty,Kind},loc)) = the_abs_type Ty
  | the_abs_type(PT(TyRankConstr{Ty,Rank},loc)) = the_abs_type Ty
  | the_abs_type(ty as PT(TyAbst(ty1,ty2),loc)) = ty
  | the_abs_type _ = raise TCERR "the_abs_type" "not a type abstraction";

fun dom_rng ty =
  let val (tyf,ty2) = dest_app_type ty
      val (ty0,ty1) = dest_app_type tyf
      val {Thy, Tyop, Kind, Rank} = dest_con_type ty0
  in if Thy = "min" andalso Tyop = "fun" andalso Kind = Prekind.mk_arity 2 andalso Rank = Prerank.Zerorank
     then (ty1,ty2)
     else raise ERR "" ""
  end
  handle HOL_ERR _ => raise ERR "dom_rng" "not a function type";

val is_fun_type = can dom_rng

(* returns a list of strings, names of all kind variables mentioned *)
fun kindvars (PT (ty, loc)) =
  case ty of
    Vartype (_, kd, _) => Prekind.kindvars kd
  | Contype{Kind=Kind, ...} => Prekind.kindvars Kind
  | TyApp (ty1, ty2) => Lib.union (kindvars ty1) (kindvars ty2)
  | TyUniv (tyv, ty) => Lib.union (kindvars tyv) (kindvars ty)
  | TyAbst (tyv, ty) => Lib.union (kindvars tyv) (kindvars ty)
  | TyKindConstr {Ty,Kind} => Lib.union (kindvars Ty) (Prekind.kindvars Kind)
  | TyRankConstr {Ty,... } => kindvars Ty
  | UVar (ref (NONEU(kd,_))) => Prekind.kindvars kd
  | UVar (ref (SOMEU ty')) => kindvars ty'

(* returns a list of strings, names of all type variables mentioned *)
fun tyvars (PT (ty, loc)) =
  case ty of
    Vartype (s, _, _) => [s]
  | Contype s => []
  | TyApp (ty1, ty2) => Lib.union (tyvars ty1) (tyvars ty2)
  | TyUniv (tyv, ty) => Lib.union (tyvars tyv) (tyvars ty)
  | TyAbst (tyv, ty) => Lib.union (tyvars tyv) (tyvars ty)
  | TyKindConstr {Ty,...} => tyvars Ty
  | TyRankConstr {Ty,...} => tyvars Ty
  | UVar (ref (NONEU _)) => []
  | UVar (ref (SOMEU ty')) => tyvars ty'

(* returns a list of references, refs of all unification variables mentioned *)
fun uvars_of (PT(ty, loc)) =
    case ty of
      UVar r => [r]
    | TyApp (ty1, ty2) => Lib.union (uvars_of ty1) (uvars_of ty2)
    | TyUniv (tyv, ty) => Lib.union (uvars_of tyv) (uvars_of ty)
    | TyAbst (tyv, ty) => Lib.union (uvars_of tyv) (uvars_of ty)
    | TyKindConstr {Ty, ...} => uvars_of Ty
    | TyRankConstr {Ty, ...} => uvars_of Ty
    | _ => []

fun new_uvar (kd,rk) = PT (UVar(ref (NONEU(kd,rk))), locn.Loc_None)

fun all_new_uvar () = PT (UVar(ref (NONEU(Prekind.new_uvar(),Prerank.new_uvar()))), locn.Loc_None)


(*---------------------------------------------------------------------------*
 * The free type variables in a pretype.  Tail recursive (from Ken Larsen).  *
 *---------------------------------------------------------------------------*)

local val insert = Lib.op_insert eq
      val mem    = Lib.op_mem eq
      fun TV (v as PT(Vartype _,_)) B A k = if mem v B then k A
                                            else k (insert v A)
        | TV (PT(Contype _,_)) B A k      = k A
        | TV (PT(TyApp(opr, ty),_)) B A k = TV opr B A (fn q => TV ty B q k)
        | TV (PT(TyUniv(v,ty),_)) B A k   = TV ty (insert v B) A k
        | TV (PT(TyAbst(v,ty),_)) B A k   = TV ty (insert v B) A k
        | TV (PT(TyKindConstr{Ty,Kind},_)) B A k = TV Ty B A k
        | TV (PT(TyRankConstr{Ty,Rank},_)) B A k = TV Ty B A k
        | TV (v as PT(UVar(ref(NONEU _ )),_)) B A k = if mem v B then k A
                                                      else k (insert v A)
     (* | TV (PT(UVar(ref(NONEU _ )),_)) B A k = k A *)
        | TV (PT(UVar(ref(SOMEU ty)),_)) B A k = TV ty B A k
      and TVl (ty::tys) B A k = TV ty B A (fn q => TVl tys B q k)
        | TVl _ B A k = k A
in
fun type_vars ty = rev(TV ty [] [] Lib.I)
fun type_varsl L = rev(TVl L [] [] Lib.I)
end;

fun type_vars_subst (theta : (pretype,pretype)Lib.subst) = type_varsl (map #residue theta);

(*---------------------------------------------------------------------------*
 * Calculate the prekind or prerank of a pretype.                            *
 *---------------------------------------------------------------------------*)

val op ==> = Prekind.==>

local
  open Prekind
in
fun pkind_of0 (Vartype(s,kd,rk)) = kd
  | pkind_of0 (Contype{Kind, ...}) = Kind
  | pkind_of0 (TyApp(opr,arg)) = chase (pkind_of opr)
  | pkind_of0 (TyUniv _) = typ
  | pkind_of0 (TyAbst(Bvar,Body)) = pkind_of Bvar ==> pkind_of Body
  | pkind_of0 (TyKindConstr{Ty,Kind}) = Kind
  | pkind_of0 (TyRankConstr{Ty,Rank}) = pkind_of Ty
  | pkind_of0 (UVar (ref (NONEU(kd,rk)))) = kd
  | pkind_of0 (UVar (ref (SOMEU ty))) = pkind_of ty
and pkind_of (pty as PT(ty,locn)) = pkind_of0 ty
end;

local
val zero = Prerank.Zerorank
val inc  = Prerank.Sucrank
val max  = Prerank.mk_Maxrank
in
fun prank_of0 (Vartype(s,kd,rk)) = rk
  | prank_of0 (Contype{Rank, ...}) = Rank
  | prank_of0 (TyApp(opr,arg))     = max(    prank_of opr  , prank_of arg )
  | prank_of0 (TyUniv(Bvar,Body))  = max(inc(prank_of Bvar), prank_of Body)
  | prank_of0 (TyAbst(Bvar,Body))  = max(    prank_of Bvar , prank_of Body)
  | prank_of0 (TyKindConstr{Ty,Kind}) = prank_of Ty
  | prank_of0 (TyRankConstr{Ty,Rank}) = Rank
  | prank_of0 (UVar (ref (NONEU(_,rk)))) = rk
  | prank_of0 (UVar (ref (SOMEU ty))) = prank_of ty
and prank_of (PT(ty,locn)) = prank_of0 ty
end;

(*---------------------------------------------------------------------------*
 * Given a type variable and a list of type variables, if the type variable  *
 * does not exist on the list, then return the type variable. Otherwise,     *
 * rename the type variable and try again. Note well that the variant uses   *
 * only the name of the variable as a basis for testing equality. Experience *
 * has shown that basing the comparison on all of the name, the arity, the   *
 * rank, and the type arguments of the variable resulted in needlessly       *
 * confusing formulas occasionally being displayed in interactive sessions.  *
 *---------------------------------------------------------------------------*)

fun gen_variant caller =
  let fun var_name (PT(Vartype(Name,_,_),_)) = Name
        | var_name _ = raise ERR caller "not a variable"
      fun vary vlist (PT(Vartype(Name,Kind,Rank),locn)) =
          let val L = map var_name (filter is_var_type vlist)
              val next = Lexis.gen_variant Lexis.tyvar_vary L
              fun loop name =
                 let val s = if mem name L then next name else name
                 in s
                 end
          in PT(Vartype(loop Name, Kind, Rank),locn)
          end
        | vary _ _ = raise ERR caller "2nd argument should be a variable"
  in vary
  end;

fun variant_type fvs v = if is_var_type v then gen_variant "variant_type" fvs v
                            else (* v is a uvar *)
                            if op_mem eq v fvs then new_uvar(pkind_of v,prank_of v)
                            else v


(*---------------------------------------------------------------------------*
 *    Section on substitution.                                               *
 *---------------------------------------------------------------------------*)

fun apply_subst subst (pt as PT (pty, locn)) =
  case pty of
    Vartype _ => pt
  | Contype _ => pt
  | TyApp(ty1, ty2) => PT (TyApp(apply_subst subst ty1, apply_subst subst ty2), locn)
  | TyUniv(bty, body) => PT (TyUniv(apply_subst subst bty, apply_subst subst body), locn)
  | TyAbst(bty, body) => PT (TyAbst(apply_subst subst bty, apply_subst subst body), locn)
  | TyKindConstr {Ty, Kind} =>
                 PT (TyKindConstr {Ty=apply_subst subst Ty, Kind=Kind}, locn)
  | TyRankConstr {Ty, Rank} =>
                 PT (TyRankConstr {Ty=apply_subst subst Ty, Rank=Rank}, locn)
  | UVar (ref (SOMEU t)) => apply_subst subst t
  | UVar (r as ref (NONEU _)) =>
      case (Lib.assoc1 r subst) of
        NONE => pt
      | SOME (_, value) => apply_subst subst value


(*---------------------------------------------------------------------------*
 *    Converting pretypes to strings, for printing.                          *
 *---------------------------------------------------------------------------*)

fun kind_rank_to_string (kd,rk) =
    if current_trace "kinds" = 0 then "" else
      let open Prekind Prerank
      in   (if prekind_compare(kd,typ) = EQUAL
            then "" else ":" ^ prekind_to_string kd)
         ^ (if prerank_compare(rk,Zerorank) = EQUAL
            then "" else ":<=" ^ prerank_to_string rk)
      end

datatype pp_pty_state = none | left | right | uvar

fun pp_pretype pps ty =
 let open Portable
     val {add_string,add_break,begin_block,end_block,...} = with_ppstream pps
     val checkref = Portable.ref_to_int
     fun pppretype state (ty as PT(ty0,locn)) =
       case ty0 of
           UVar(r as ref (SOMEU pty')) => let
           in
             if state <> uvar then begin_block INCONSISTENT 0 else ();
             add_string (Int.toString (checkref r) ^ ":");
             add_break (1,2);
             pppretype uvar pty';
             if state <> uvar then end_block() else ()
           end
         | UVar(r as ref (NONEU(kd,rk))) => add_string (Int.toString (checkref r) ^ kind_rank_to_string(kd,rk))
         | Vartype(s,kd,rk) => add_string ("V(" ^ s ^ kind_rank_to_string(kd,rk) ^ ")")
         | Contype {Thy, Tyop, Kind, Rank} => if Thy = "bool" orelse Thy = "min" then
                                                add_string Tyop
                                              else add_string (Thy ^ "$" ^ Tyop) (* ^ kind_rank_to_string(Kind,Rank) *)
         | TyApp(PT(TyApp(PT(Contype{Tyop="fun",...},_), ty1),_), ty2) =>
                              (if state = none then begin_block INCONSISTENT 0
                               else if state = left orelse state = uvar then
                                   (add_string "("; begin_block INCONSISTENT 0)
                               else ();
                               pppretype left ty1;
                               add_string " ->";
                               add_break(1,0);
                               pppretype right ty2;
                               if state = none then end_block()
                               else if state = left orelse state = uvar then
                                  (end_block(); add_string ")")
                               else ())
         | TyApp(PT(UVar(ref(SOMEU(PT(TyApp(PT(Contype{Tyop="fun",...},_), ty1),_)))),_), ty2) =>
                              (if state = none then begin_block INCONSISTENT 0
                               else if state = left orelse state = uvar then
                                   (add_string "("; begin_block INCONSISTENT 0)
                               else ();
                               pppretype left ty1;
                               add_string " ->";
                               add_break(1,0);
                               pppretype right ty2;
                               if state = none then end_block()
                               else if state = left orelse state = uvar then
                                  (end_block(); add_string ")")
                               else ())
         | TyApp(PT(TyApp(PT(Contype{Tyop="prod",...},_), ty1),_), ty2) =>
                              (if state = none then begin_block INCONSISTENT 0
                               else if state = left orelse state = uvar then
                                   (add_string "("; begin_block INCONSISTENT 0)
                               else ();
                               pppretype left ty1;
                               add_string " #";
                               add_break(1,0);
                               pppretype right ty2;
                               if state = none then end_block()
                               else if state = left orelse state = uvar then
                                  (end_block(); add_string ")")
                               else ())
         | TyApp(PT(TyApp(PT(Contype{Tyop="sum",...},_), ty1),_), ty2) =>
                              (if state = none then begin_block INCONSISTENT 0
                               else if state = left orelse state = uvar then
                                   (add_string "("; begin_block INCONSISTENT 0)
                               else ();
                               pppretype left ty1;
                               add_string " +";
                               add_break(1,0);
                               pppretype right ty2;
                               if state = none then end_block()
                               else if state = left orelse state = uvar then
                                  (end_block(); add_string ")")
                               else ())
         | TyApp(ty1, ty2) => (add_string "(";
                               begin_block INCONSISTENT 0;
                               pppretype none ty2;
                               add_break(1,0);
                               pppretype none ty1;
                               end_block();
                               add_string ")")
         | TyUniv(tyv, ty) => (add_string "(!";
                               begin_block INCONSISTENT 0;
                               pppretype none tyv;
                               add_string ".";
                               add_break(1,2);
                               pppretype none ty;
                               end_block();
                               add_string ")")
         | TyAbst(tyv, ty) => (add_string "(\\";
                               begin_block INCONSISTENT 0;
                               pppretype none tyv;
                               add_string ".";
                               add_break(1,2);
                               pppretype none ty;
                               end_block();
                               add_string ")")
         | TyKindConstr {Ty, Kind} =>
                              (begin_block INCONSISTENT 0;
                               pppretype none Ty;
                               add_string " :";
                               add_break(1,2);
                               add_string (kind_to_string(Prekind.toKind Kind));
                               end_block())
         | TyRankConstr {Ty, Rank} =>
                              (begin_block INCONSISTENT 0;
                               pppretype none Ty;
                               add_string " :<=";
                               add_break(1,2);
                               add_string (Int.toString(Prerank.toRank Rank));
                               end_block())
 in
   pppretype none ty
 end;

val pretype_to_string = Portable.pp_to_string 80 pp_pretype
fun print_pretype ty = Portable.output(Portable.std_out, pretype_to_string ty);

fun pp_pretypes pps tys =
 let open Portable
     val {add_string,add_break,begin_block,end_block,...} = with_ppstream pps
     val pp_pretype = pp_pretype pps
     fun pppretypes0 [] = ()
       | pppretypes0 (ty::tys) = (add_string ",";
                                  add_break(0,0);
                                  pp_pretype ty;
                                  pppretypes0 tys)
     fun pppretypes [] = ()
       | pppretypes (ty::tys) =  (begin_block INCONSISTENT 0;
                                  pp_pretype ty;
                                  pppretypes0 tys;
                                  end_block())
 in
   add_string "[";
   pppretypes tys;
   add_string "]"
 end;

val pretypes_to_string = Portable.pp_to_string 80 pp_pretypes
fun print_pretypes tys = Portable.output(Portable.std_out, pretypes_to_string tys);

(*
let
  fun with_pp ppfn pps x =
      Parse.respect_width_ref Globals.linewidth ppfn pps x handle e => Raise e
in
  installPP (with_pp pp_pretype)
end;
*)


(*------------------------------------------------------------------------------*
 * Replace variable or unification variable subpretypes in a pretype. Renaming. *
 *------------------------------------------------------------------------------*)

local
  val is_var_subst = Lib.all (fn {redex,residue} => has_var_type redex)
  fun peek ([], x) = NONE
    | peek ({redex=a, residue=b}::l, x) = if eq a x then SOME b else peek (l, x)
  fun insert(theta,v,v') = (v |-> v')::theta
  fun delete((r as {redex=a, residue=b})::l, v) = if eq a v then delete(l,v)
                                                  else r :: delete(l,v)
    | delete([],v) = []
in
fun type_subst [] = I
  | type_subst theta =
    let fun vsubs0 fmap (v as Vartype _) =
               (case peek(fmap,PT(v, locn.Loc_None)) of
                                     NONE => v
                                   | SOME (PT(y,_)) => y)
          | vsubs0 fmap (v as UVar (ref(NONEU(kd,rk)))) =
               (case peek(fmap,PT(v, locn.Loc_None)) of
                                     NONE => v
                                   | SOME (PT(y,_)) => y)
          | vsubs0 fmap (TyApp(opr,ty)) = TyApp(vsubs fmap opr, vsubs fmap ty)
          | vsubs0 fmap (TyUniv(Bvar,Body)) =
               let val Bvar1 = the_var_type Bvar
                   val fmap = delete(fmap,Bvar1)
                   val frees = type_vars_subst fmap
                   val fvs = Lib.op_set_diff eq (type_vars Body) [Bvar1]
                   val Bvar' = variant_type (Lib.op_union eq frees fvs) Bvar1
               in if eq Bvar1 Bvar' then TyUniv(Bvar, vsubs fmap Body)
                  else let val fmap' = insert(fmap,Bvar1,Bvar')
                       in TyUniv(vsubs fmap' Bvar, vsubs fmap' Body)
                       end
               end
          | vsubs0 fmap (TyAbst(Bvar,Body)) =
               let val Bvar1 = the_var_type Bvar
                   val fmap = delete(fmap,Bvar1)
                   val frees = type_vars_subst fmap
                   val fvs = Lib.op_set_diff eq (type_vars Body) [Bvar1]
                   val Bvar' = variant_type (Lib.op_union eq frees fvs) Bvar1
               in if eq Bvar1 Bvar' then TyAbst(Bvar, vsubs fmap Body)
                  else let val fmap' = insert(fmap,Bvar1,Bvar')
                       in TyAbst(vsubs fmap' Bvar, vsubs fmap' Body)
                       end
               end
          | vsubs0 fmap (TyKindConstr{Ty,Kind}) =
                         TyKindConstr{Ty=vsubs fmap Ty,Kind=Kind}
          | vsubs0 fmap (TyRankConstr{Ty,Rank}) =
                         TyRankConstr{Ty=vsubs fmap Ty,Rank=Rank}
          | vsubs0 fmap (UVar (r as ref(SOMEU (PT(ty,_))))) = vsubs0 fmap ty
          | vsubs0 fmap t = t
        and vsubs fmap (PT(ty,locn)) = PT(vsubs0 fmap ty,locn)
        fun subs fmap (ty as PT(ty0,locn)) =
          case peek(fmap,ty)
           of SOME residue => residue
            | NONE =>
              (case ty0
                of TyApp(opr,ty) => PT(TyApp(subs fmap opr, subs fmap ty), locn)
                 | TyUniv(Bvar,Body) =>
                     let val Bvar1 = the_var_type Bvar
                         val frees = type_vars_subst fmap
                         val fvs = Lib.op_set_diff eq (type_vars Body) [Bvar1]
                         val Bvar' = variant_type (Lib.op_union eq frees fvs) Bvar1
                     in if eq Bvar1 Bvar' then PT(TyUniv(Bvar, subs fmap Body), locn)
                        else let val fmap' = insert(fmap,Bvar1,Bvar')
                             in PT(TyUniv(subs fmap' Bvar, subs fmap' Body), locn)
                             end
                     end
                 | TyAbst(Bvar,Body) =>
                     let val Bvar1 = the_var_type Bvar
                         val frees = type_vars_subst fmap
                         val fvs = Lib.op_set_diff eq (type_vars Body) [Bvar1]
                         val Bvar' = variant_type (Lib.op_union eq frees fvs) Bvar1
                     in if eq Bvar1 Bvar' then PT(TyAbst(Bvar, subs fmap Body), locn)
                        else let val fmap' = insert(fmap,Bvar1,Bvar')
                             in PT(TyAbst(subs fmap' Bvar, subs fmap' Body), locn)
                             end
                     end
                 | TyKindConstr{Ty,Kind} =>
                     PT(TyKindConstr{Ty=subs fmap Ty, Kind=Kind}, locn)
                 | TyRankConstr{Ty,Rank} =>
                     PT(TyRankConstr{Ty=subs fmap Ty, Rank=Rank}, locn)
                 | UVar (r as ref(SOMEU ty)) => subs fmap ty
                 | _ => ty)
    in
      (if is_var_subst theta then vsubs else subs) theta
    end
end;


fun distinguish_btyvars context_tyvars =
    let fun dbvs0 cxvs (TyApp(opr,arg)) = TyApp(dbvs cxvs opr, dbvs cxvs arg)
          | dbvs0 cxvs (TyUniv(Bvar,Body)) =
               let val Bvar1 = the_var_type Bvar
                   val fvs = Lib.op_set_diff eq (type_vars Body) [Bvar1]
                   val Bvar' = variant_type (Lib.op_union eq cxvs fvs) Bvar1
                   val cxvs' = Bvar'::cxvs
               in if eq Bvar1 Bvar' then TyUniv(Bvar, dbvs cxvs' Body)
                  else let val instfn = type_subst [Bvar1 |-> Bvar']
                       in TyUniv(instfn Bvar, dbvs cxvs' (instfn Body))
                       end
               end
          | dbvs0 cxvs (TyAbst(Bvar,Body)) =
               let val Bvar1 = the_var_type Bvar
                   val fvs = Lib.op_set_diff eq (type_vars Body) [Bvar1]
                   val Bvar' = variant_type (Lib.op_union eq cxvs fvs) Bvar1
                   val cxvs' = Bvar'::cxvs
               in if eq Bvar1 Bvar' then TyAbst(Bvar, dbvs cxvs' Body)
                  else let val instfn = type_subst [Bvar1 |-> Bvar']
                       in TyAbst(instfn Bvar, dbvs cxvs' (instfn Body))
                       end
               end
          | dbvs0 cxvs (TyKindConstr{Ty,Kind}) =
                         TyKindConstr{Ty=dbvs cxvs Ty,Kind=Kind}
          | dbvs0 cxvs (TyRankConstr{Ty,Rank}) =
                         TyRankConstr{Ty=dbvs cxvs Ty,Rank=Rank}
          | dbvs0 cxvs (UVar (r as ref(SOMEU ty))) =
                        (r := SOMEU (dbvs cxvs ty);
                         UVar r)
          | dbvs0 cxvs t = t
        and dbvs cxvs (PT(ty,locn)) = PT(dbvs0 cxvs ty,locn)
    in
      dbvs context_tyvars
    end;



local
val EERR = ERR "eta_conv_ty" "not a type eta redex"
in
fun eta_conv_ty (PT(TyAbst(Bvar, M), _))
       = let
(*           val _ = if not (is_debug()) then () else
                     print ("eta_conv_ty: Bvar = " ^ pretype_to_string Bvar ^ "\n"
                          ^ "             M = " ^ pretype_to_string M ^ "\n")
*)
             val (Opr,Arg) = dest_app_type M
                              handle HOL_ERR _ => raise EERR
(*
             val _ = if not (is_debug()) then () else
                     print ("eta_conv_ty: Opr = " ^ pretype_to_string Opr ^ "\n"
                          ^ "             Arg = " ^ pretype_to_string Arg ^ "\n")
*)
             val  Bvar0     = the_var_type Bvar
                              handle HOL_ERR _ => raise EERR
             val  Argv      = the_var_type Arg
                              handle HOL_ERR _ => raise EERR
(*
             val _ = if not (is_debug()) then () else
                     print ("eta_conv_ty: Bvar0 = " ^ pretype_to_string Bvar0 ^ "\n"
                          ^ "             Argv  = " ^ pretype_to_string Argv  ^ "\n")
*)
             val _ = if eq Bvar0 Argv then () else raise EERR
(*
             val _ = if not (is_debug()) then () else
                     print ("eta_conv_ty: bound var and arg are same; about to check bound var not in Opr\n");
*)
             val _ = if Lib.op_mem eq Bvar0 (type_vars Opr) then raise EERR else ()
(*
             val _ = if not (is_debug()) then () else
                     print ("bound var not in Opr\n")
*)
         in Opr
         end
  | eta_conv_ty _ = raise EERR
end



local
val BERR = ERR "beta_conv_ty" "not a type beta redex"
in
fun beta_conv_ty (PT(TyApp(M, N), _))
       = let
(*           val _ = if not (is_debug()) then () else
                     print ("beta_conv_ty: M = " ^ pretype_to_string M ^ "\n"
                          ^ "              N = " ^ pretype_to_string N ^ "\n")
*)
             val (Bnd,Body) = dest_abs_type (the_abs_type M)
                              handle HOL_ERR _ => raise BERR
(*
             val _ = if not (is_debug()) then () else
                     print ("beta_conv_ty: Bnd  = " ^ pretype_to_string Bnd  ^ "\n"
                          ^ "              Body = " ^ pretype_to_string Body ^ "\n")
*)
             val  Bvar      = the_var_type Bnd
                              handle HOL_ERR _ => raise BERR
(*
             val _ = if not (is_debug()) then () else
                     print ("beta_conv_ty: Bvar = " ^ pretype_to_string Bvar ^ "\n")
*)
             val _ = Prekind.unify (pkind_of N) (pkind_of Bvar);
             val _ = Prerank.unify_le (prank_of N) (* <= *) (prank_of Bvar);
(*
             val _ = if not (is_debug()) then () else
                     print ("beta_conv_ty: kind and rank unified; about to subst\n");
*)
             val Res = type_subst [Bvar |-> N] Body
                       handle e => Raise e
(*
             val _ = if not (is_debug()) then () else
                     print ("beta_conv_ty: Res  = " ^ pretype_to_string Res ^ "\n")
*)
         in Res
         end
  | beta_conv_ty _ = raise BERR
end

exception UNCHANGEDTY;

fun qconv_ty c ty = c ty handle UNCHANGEDTY => ty

(* ---------------------------------------------------------------------*)
(* rand_conv_ty conv ``:t2 t1`` applies conv to t2                      *)
(* ---------------------------------------------------------------------*)

fun rand_conv_ty conv (PT(TyApp(Rator,Rand), locn)) = let
  val Newrand = conv Rand
    handle HOL_ERR {origin_function, message, origin_structure} =>
      if Lib.mem origin_function
           ["rand_conv_ty", "rator_conv_ty", "abs_conv_ty", "univ_conv_ty", "uvar_conv_ty"]
         andalso origin_structure = "Pretype"
      then
        raise ERR "rand_conv_ty" message
      else
        raise ERR "rand_conv_ty" (origin_function ^ ": " ^ message)
in
  PT(TyApp(Rator, Newrand), locn)
end
  | rand_conv_ty conv _ = raise ERR "rand_conv_ty" "not a pretype application"

(* ---------------------------------------------------------------------*)
(* rator_conv_ty conv ``:t2 t1`` applies conv to t1                     *)
(* ---------------------------------------------------------------------*)

fun rator_conv_ty conv (PT(TyApp(Rator,Rand), locn)) = let
  val Newrator = conv Rator
    handle HOL_ERR {origin_function, message, origin_structure} =>
      if Lib.mem origin_function
           ["rand_conv_ty", "rator_conv_ty", "abs_conv_ty", "univ_conv_ty", "uvar_conv_ty"]
         andalso origin_structure = "Pretype"
      then
        raise ERR "rator_conv_ty" message
      else
        raise ERR "rator_conv_ty" (origin_function ^ ": " ^ message)
in
  PT(TyApp(Newrator, Rand), locn)
end
  | rator_conv_ty conv _ = raise ERR "rator_conv_ty" "not a pretype application"

(* ----------------------------------------------------------------------
    abs_conv_ty conv ``: \'a. t['a]`` applies conv to t['a]
   ---------------------------------------------------------------------- *)

fun abs_conv_ty conv (PT(TyAbst(Bvar,Body), locn)) = let
  val Newbody = conv Body
    handle HOL_ERR {origin_function, message, origin_structure} =>
      if Lib.mem origin_function
           ["rand_conv_ty", "rator_conv_ty", "abs_conv_ty", "univ_conv_ty", "uvar_conv_ty"]
         andalso origin_structure = "Pretype"
      then
        raise ERR "abs_conv_ty" message
      else
        raise ERR "abs_conv_ty" (origin_function ^ ": " ^ message)
in
  PT(TyAbst(Bvar, Newbody), locn)
end
  | abs_conv_ty conv _ = raise ERR "abs_conv_ty" "not a pretype abstraction"

(* ----------------------------------------------------------------------
    kind_constr_conv_ty conv ``: t : k`` applies conv to t
   ---------------------------------------------------------------------- *)

fun kind_constr_conv_ty conv (PT(TyKindConstr{Ty,Kind}, locn)) = let
  val Newty = conv Ty
    handle HOL_ERR {origin_function, message, origin_structure} =>
      if Lib.mem origin_function
           ["rand_conv_ty", "rator_conv_ty", "abs_conv_ty", "univ_conv_ty", "uvar_conv_ty"]
         andalso origin_structure = "Pretype"
      then
        raise ERR "kind_constr_conv_ty" message
      else
        raise ERR "kind_constr_conv_ty" (origin_function ^ ": " ^ message)
in
  PT(TyKindConstr{Ty=Newty,Kind=Kind}, locn)
end
  | kind_constr_conv_ty conv _ = raise ERR "kind_constr_conv_ty" "not a pretype kind constraint"

(* ----------------------------------------------------------------------
    rank_constr_conv_ty conv ``: t : k`` applies conv to t
   ---------------------------------------------------------------------- *)

fun rank_constr_conv_ty conv (PT(TyRankConstr{Ty,Rank}, locn)) = let
  val Newty = conv Ty
    handle HOL_ERR {origin_function, message, origin_structure} =>
      if Lib.mem origin_function
           ["rand_conv_ty", "rator_conv_ty", "abs_conv_ty", "univ_conv_ty", "uvar_conv_ty"]
         andalso origin_structure = "Pretype"
      then
        raise ERR "rank_constr_conv_ty" message
      else
        raise ERR "rank_constr_conv_ty" (origin_function ^ ": " ^ message)
in
  PT(TyRankConstr{Ty=Newty,Rank=Rank}, locn)
end
  | rank_constr_conv_ty conv _ = raise ERR "rank_constr_conv_ty" "not a pretype rank constraint"

(* ----------------------------------------------------------------------
    univ_conv_ty conv ``: !'a. t['a]`` applies conv to t['a]
   ---------------------------------------------------------------------- *)

fun univ_conv_ty conv (PT(TyUniv(Bvar,Body), locn)) = let
  val Newbody = conv Body
    handle HOL_ERR {origin_function, message, origin_structure} =>
      if Lib.mem origin_function
           ["rand_conv_ty", "rator_conv_ty", "abs_conv_ty", "univ_conv_ty", "uvar_conv_ty"]
         andalso origin_structure = "pretype"
      then
        raise ERR "univ_conv_ty" message
      else
        raise ERR "univ_conv_ty" (origin_function ^ ": " ^ message)
in
  PT(TyUniv(Bvar, Newbody), locn)
end
  | univ_conv_ty conv _ = raise ERR "univ_conv_ty" "not a universal pretype"

(* ----------------------------------------------------------------------
    uvar_conv_ty conv (Uvar (SOMEU ty)) applies conv to ty
   ---------------------------------------------------------------------- *)

fun uvar_conv_ty conv (PT(UVar (r as ref (SOMEU ty)), locn)) = let
  val Newty = conv ty
    handle HOL_ERR {origin_function, message, origin_structure} =>
      if Lib.mem origin_function
           ["rand_conv_ty", "rator_conv_ty", "abs_conv_ty", "univ_conv_ty", "uvar_conv_ty"]
         andalso origin_structure = "Pretype"
      then
        raise ERR "univ_conv_ty" message
      else
        raise ERR "univ_conv_ty" (origin_function ^ ": " ^ message)
in
  (* Newty *)
  PT(UVar (ref (SOMEU Newty)), locn) (* creates a new reference to hold the converted value *)
end
  | uvar_conv_ty conv (ty as PT(UVar (ref (NONEU _)), locn)) = raise UNCHANGEDTY (* unchanged *)
  | uvar_conv_ty conv _ = raise ERR "uvar_conv_ty" "not a pretype unification var"

(*---------------------------------------------------------------------------
 * Conversion that always fails;  identity element for orelse_ty.
 *---------------------------------------------------------------------------*)

fun no_conv_ty _ = raise ERR "no_conv_ty" "";

(* ----------------------------------------------------------------------
    Conversion that always succeeds, but does nothing.
    Indicates this by raising the UNCHANGEDTY exception.
   ---------------------------------------------------------------------- *)

fun all_conv_ty _ = raise UNCHANGEDTY;

(* ----------------------------------------------------------------------
    Apply two conversions in succession;  fail if either does.  Handle
    UNCHANGED appropriately.
   ---------------------------------------------------------------------- *)

infix then_ty orelse_ty;

fun (conv1 then_ty conv2) ty = let
  val ty1 = conv1 ty
in
  conv2 ty1 handle UNCHANGEDTY => ty1
end handle UNCHANGEDTY => conv2 ty

(* ----------------------------------------------------------------------
    Apply conv1;  if it raises a HOL_ERR then apply conv2. Note that
    interrupts and other exceptions (including UNCHANGEDTY) will sail on
    through.
   ---------------------------------------------------------------------- *)

fun (conv1 orelse_ty conv2) ty = conv1 ty handle HOL_ERR _ => conv2 ty;


(*---------------------------------------------------------------------------*
 * Perform the first successful conversion of those in the list.             *
 *---------------------------------------------------------------------------*)

fun first_conv_ty [] ty = no_conv_ty ty
  | first_conv_ty (a::rst) ty = a ty handle HOL_ERR _ => first_conv_ty rst ty;

(*---------------------------------------------------------------------------
 * Perform every conversion in the list.
 *---------------------------------------------------------------------------*)

fun every_conv_ty convl ty =
   itlist (curry (op then_ty)) convl all_conv_ty ty
   handle HOL_ERR _ => raise ERR "every_conv_ty" "";


(*---------------------------------------------------------------------------
 * Cause the conversion to fail if it does not change its input.
 *---------------------------------------------------------------------------*)

fun changed_conv_ty conv ty =
   let val ty1 = conv ty
           handle UNCHANGEDTY => raise ERR "changed_conv_ty" "Input type unchanged"
   in if eq ty ty1 then raise ERR"changed_conv_ty" "Input type unchanged"
      else ty1
   end;

(* ----------------------------------------------------------------------
    Cause a failure if the conversion causes the UNCHANGED exception to
    be raised.  Doesn't "waste time" doing an equality check.  Mnemonic:
    "quick changed_conv".
   ---------------------------------------------------------------------- *)

fun qchanged_conv_ty conv ty =
    conv ty
    handle UNCHANGEDTY => raise ERR "qchanged_conv_ty" "Input type unchanged"

(*---------------------------------------------------------------------------
 * Apply a conversion zero or more times.
 *---------------------------------------------------------------------------*)

fun repeat_ty conv ty =
    ((qchanged_conv_ty conv then_ty (repeat_ty conv)) orelse_ty all_conv_ty) ty;

fun try_conv_ty conv = conv orelse_ty all_conv_ty;

fun app_conv_ty conv (PT(TyApp(Rator,Rand), locn)) = let
in
  let val Rator' = conv Rator
  in
    PT(TyApp(Rator', conv Rand), locn) handle UNCHANGEDTY => PT(TyApp(Rator', Rand), locn)
  end handle UNCHANGEDTY => PT(TyApp(Rator, conv Rand), locn)
end
  | app_conv_ty conv _ = raise ERR "app_conv_ty" "not a pretype application"

fun sub_conv_ty conv =
    try_conv_ty (app_conv_ty conv orelse_ty abs_conv_ty conv orelse_ty univ_conv_ty conv
                 orelse_ty kind_constr_conv_ty conv orelse_ty rank_constr_conv_ty conv
                 orelse_ty uvar_conv_ty conv)

fun head_sub_conv_ty conv =
    try_conv_ty (rator_conv_ty conv
                 orelse_ty kind_constr_conv_ty conv orelse_ty rank_constr_conv_ty conv
                 orelse_ty uvar_conv_ty conv)

(* ----------------------------------------------------------------------
    traversal conversionals.

    depth_conv_ty c
      bottom-up, recurse over sub-terms, and then repeatedly apply c at
      top-level.

    redepth_conv_ty c
      bottom-up. recurse over sub-terms, apply c at top, and if this
      succeeds, repeat from start.

    top_depth_conv_ty c
      top-down. Repeatdly apply c at top-level, then descend.  If descending
      doesn't change anything then stop.  If there was a change then
      come back to top and try c once more at top-level.  If this succeeds
      repeat.

    top_sweep_conv_ty c
      top-down.  Like top_depth_conv_ty but only makes one pass over the term,
      never coming back to the top level once descent starts.

    once_depth_conv_ty c
      top-down (confusingly).  Descends term looking for position at
      which c works.  Does this "in parallel", so c may be applied multiple
      times at highest possible positions in distinct sub-terms.

   ---------------------------------------------------------------------- *)

fun depth_conv_ty conv ty =
    (sub_conv_ty (depth_conv_ty conv) then_ty repeat_ty conv) ty

fun redepth_conv_ty conv ty =
    (sub_conv_ty (redepth_conv_ty conv) then_ty
     try_conv_ty (conv then_ty redepth_conv_ty conv)) ty

fun top_depth_conv_ty conv ty =
    (repeat_ty conv then_ty
     try_conv_ty (changed_conv_ty (sub_conv_ty (top_depth_conv_ty conv)) then_ty
                  try_conv_ty (conv then_ty top_depth_conv_ty conv))) ty

fun once_depth_conv_ty conv ty =
    try_conv_ty (conv orelse_ty sub_conv_ty (once_depth_conv_ty conv)) ty

fun top_sweep_conv_ty conv ty =
    (repeat_ty conv then_ty sub_conv_ty (top_sweep_conv_ty conv)) ty

val deep_beta_ty = qconv_ty (top_depth_conv_ty beta_conv_ty)

val deep_eta_ty = qconv_ty (top_depth_conv_ty eta_conv_ty)

val deep_beta_eta_ty = qconv_ty (top_depth_conv_ty (beta_conv_ty orelse_ty eta_conv_ty))

(*  head_ty returns the head of the given type. *)
fun head_ty (PT(TyApp(ty1,ty2)            ,locn)) = head_ty ty1
  | head_ty (PT(TyKindConstr{Ty,Kind}     ,locn)) = head_ty Ty
  | head_ty (PT(TyRankConstr{Ty,Rank}     ,locn)) = head_ty Ty
  | head_ty (PT(UVar (r as ref (SOMEU ty)),locn)) = head_ty ty
  | head_ty ty = ty

(*  head_beta1_ty reduces the head beta redex; fails if one does not exist. *)
fun head_beta1_ty (ty as PT(TyApp(ty1,ty2),locn)) =
       (rator_conv_ty head_beta1_ty orelse_ty beta_conv_ty) ty
(*
       if is_abs_type ty1 then beta_conv_ty ty
       else PT(TyApp(head_beta1_ty ty1,ty2),locn)
*)
  | head_beta1_ty (PT(TyKindConstr{Ty,Kind},locn)) =
       PT(TyKindConstr{Ty=head_beta1_ty Ty,Kind=Kind},locn)
  | head_beta1_ty (PT(TyRankConstr{Ty,Rank},locn)) =
       PT(TyRankConstr{Ty=head_beta1_ty Ty,Rank=Rank},locn)
  | head_beta1_ty (PT(UVar (r as ref (SOMEU ty)),locn)) =
       (r := SOMEU (head_beta1_ty ty); PT(UVar r,locn))
  | head_beta1_ty _ = raise ERR "head_beta1_ty" "no beta redex found"

(*  head_beta_ty repeatedly reduces any head beta redexes; never fails *)
(*  result has at its top level its actual shape *)
val head_beta_ty = qconv_ty (repeat_ty head_beta1_ty)


val dest_univ_type = dest_univ_type0 o deep_beta_eta_ty

val is_not_univ_type = is_not_univ_type0 o deep_beta_eta_ty

fun strip_univ_type ty =
    let fun strip ty =
       let val (bvar, body1) = dest_univ_type0 ty
           val (bvars, body) = strip body1
       in (bvar::bvars, body)
       end
       handle HOL_ERR _ => ([],ty)
    in strip (deep_beta_eta_ty ty)
    end


infix ref_occurs_in

fun r ref_occurs_in (PT(value, locn)) =
  case value of
    Vartype _ => false
  | Contype _ => false
  | TyApp(ty1, ty2) => r ref_occurs_in ty1 orelse r ref_occurs_in ty2
  | TyUniv(tyv, ty) => r ref_occurs_in tyv orelse r ref_occurs_in ty
  | TyAbst(tyv, ty) => r ref_occurs_in tyv orelse r ref_occurs_in ty
  | TyKindConstr {Ty, ...} => r ref_occurs_in Ty
  | TyRankConstr {Ty, ...} => r ref_occurs_in Ty
  | UVar (r' as ref (NONEU _)) => r = r'
  | UVar (r' as ref (SOMEU t)) => r = r' orelse r ref_occurs_in t

infix ref_equiv
fun r ref_equiv (PT(value, locn)) =
  case value of
    UVar (r' as ref (NONEU _)) => r = r'
  | UVar (r' as ref (SOMEU t)) => r = r' orelse r ref_equiv t
  | _ => false

  fun has_free_uvar_kind (PT(pty,_)) =
    case pty of
      UVar (ref (NONEU(kd,_))) => Prekind.has_free_uvar kd
    | UVar (ref (SOMEU pty'))  => has_free_uvar_kind pty'
    | Vartype (_,kd,_)         => Prekind.has_free_uvar kd
    | Contype {Kind,...}       => Prekind.has_free_uvar Kind
    | TyApp(ty1, ty2)          => has_free_uvar_kind ty1 orelse has_free_uvar_kind ty2
    | TyAbst(tyv, ty)          => has_free_uvar_kind tyv orelse has_free_uvar_kind ty
    | TyUniv(tyv, ty)          => has_free_uvar_kind tyv orelse has_free_uvar_kind ty
    | TyKindConstr {Ty, Kind}  => has_free_uvar_kind Ty orelse Prekind.has_free_uvar Kind
    | TyRankConstr {Ty, Rank}  => has_free_uvar_kind Ty

  fun has_free_uvar (PT(pty,_)) =
    case pty of
      UVar (ref (NONEU _))    => true
    | UVar (ref (SOMEU pty')) => has_free_uvar pty'
    | Vartype _               => false
    | Contype _               => false
    | TyApp(ty1, ty2)         => has_free_uvar ty1 orelse has_free_uvar ty2
    | TyAbst(tyv, ty)         => has_free_uvar tyv orelse has_free_uvar ty
    | TyUniv(tyv, ty)         => has_free_uvar tyv orelse has_free_uvar ty
    | TyKindConstr {Ty, ...}  => has_free_uvar Ty
    | TyRankConstr {Ty, ...}  => has_free_uvar Ty


fun kind_unify k1 k2 (kd_env,rk_env,ty_env) =
  let val (kd_env', result) = Prekind.unsafe_unify k1 k2 kd_env
  in ((kd_env',rk_env,ty_env), result)
  end

fun rank_unify r1 r2 (kd_env,rk_env,ty_env) =
  let val (rk_env', result) = Prerank.unsafe_unify r1 r2 rk_env
  in if not (is_debug()) then () else
     case result of SOME _ => () | NONE =>
         (print "\nrank_unify failed:\n";
          print (Prerank.prerank_to_string r1 ^ " compared to\n" ^
                 Prerank.prerank_to_string r2 ^ "\n"));
     ((kd_env,rk_env',ty_env), result)
  end

fun rank_unify_le r1 r2 (kd_env,rk_env,ty_env) =
  let val (rk_env', result) = Prerank.unsafe_unify_le r1 r2 rk_env
  in if not (is_debug()) then () else
     case result of SOME _ => () | NONE =>
         (print "\nrank_unify_le failed:\n";
          print (Prerank.prerank_to_string r1 ^ " compared to\n" ^
                 Prerank.prerank_to_string r2 ^ "\n"));
     ((kd_env,rk_env',ty_env), result)
  end

fun deref (env as (kd_env,rk_env,ty_env)) (ty as PT(ty0,loc0)) =
  case ty0
   of UVar (r as ref (SOMEU ty')) => deref env ty'
    | UVar r => (case Lib.assoc1 r ty_env
                  of SOME (_, SOMEU ty') => deref env ty'
                   | _ => ty)
    | _ => ty

(*---------------------------------------------------------------------------*
 * The free type variables in a pretype, with dereferencing via an environment.
 *---------------------------------------------------------------------------*)

local val insert = Lib.op_insert eq
      val mem    = Lib.op_mem eq
      fun TV (v as PT(Vartype _,_)) E B A k = if mem v B then k A
                                              else k (insert v A)
        | TV (PT(Contype _,_)) E B A k      = k A
        | TV (PT(TyApp(opr, ty),_)) E B A k = TV opr E B A (fn q => TV ty E B q k)
        | TV (PT(TyUniv(v,ty),_)) E B A k   = TV ty E (insert v B) A k
        | TV (PT(TyAbst(v,ty),_)) E B A k   = TV ty E (insert v B) A k
        | TV (PT(TyKindConstr{Ty,Kind},_)) E B A k = TV Ty E B A k
        | TV (PT(TyRankConstr{Ty,Rank},_)) E B A k = TV Ty E B A k
        | TV (v as PT(UVar(ref(NONEU _ )),_)) E B A k =
                 (case deref E v
                   of (v as PT(UVar(ref(NONEU _ )),_)) => if mem v B then k A
                                                          else k (insert v A)
                    | w => TV w E B A k)
     (* | TV (PT(UVar(ref(NONEU _ )),_)) E B A k = k A *)
        | TV (PT(UVar(ref(SOMEU ty)),_)) E B A k = TV ty E B A k
      and TVl (ty::tys) E B A k = TV ty E B A (fn q => TVl tys E B q k)
        | TVl _ E B A k = k A
in
fun deref_type_vars E ty = rev(TV ty E [] [] Lib.I)
fun deref_type_varsl E L = rev(TVl L E [] [] Lib.I)
end;


fun unsafe_bind f r value =
  if r ref_equiv value
  then ok
  else if r ref_occurs_in value orelse isSomeU (!r)
       then fail
    else (fn (kd_env,rk_env,acc) =>
             (((kd_env,rk_env,(r, !r)::acc), SOME ()) before r := SOMEU value))


(* first argument is a function which performs a binding between a
   pretype reference and another pretype, updating some sort of environment
   (the 'a), returning the new alpha and a unit option, SOME () for a
   success, and a NONE, if not.

   To further complicate things, the bind argument also gets a copy of
   gen_unify to call, if it should choose.
*)
(* The environment "e" should be a triple:
     a kind environment CROSS a rank environment CROSS the prior type environment.  *)
(* this will need changing *)
(* eta-expansion *is* necessary *)
fun gen_unify (kind_unify   :prekind -> prekind -> ('a -> 'a * unit option))
              (rank_unify   :prerank -> prerank -> ('a -> 'a * unit option))
              (rank_unify_le:prerank -> prerank -> ('a -> 'a * unit option))
              bind tyvars c1 c2 (ty1 as PT(t1,locn1)) (ty2 as PT(t2,locn2)) e = let
  val gen_unify = gen_unify kind_unify rank_unify rank_unify_le bind tyvars
(*
  val ty1s = pretype_to_string ty1
  val ty2s = pretype_to_string ty2
  val ty1bs = pretype_to_string (deep_beta_eta_ty ty1)
  val ty2bs = pretype_to_string (deep_beta_eta_ty ty2)
  val _ = if is_debug() then print ("gen_unify " ^ ty1s
                                ^ "\n   (beta) " ^ ty1bs
                                ^ "\n      vs. " ^ ty2s
                                ^ "\n   (beta) " ^ ty2bs ^ "\n")
                        else ()
  val fail = fn e => (if not (is_debug()) then () else
                      print ("gen_unify fails on " ^ ty1s
                         ^ "\n               vs. " ^ ty2s ^ "\n");
                      fail e)
*)
  (* unify_var's input should be a pretype variable (possibly constrained),
       not a constant, application, abstraction, or universal type.
     unify_var's result should be either Vartype or UVar(NONEU). *)
  fun unify_var (PT(TyKindConstr{Ty=ty,Kind=kd},_)) =
         kind_unify (pkind_of ty) kd >> unify_var ty
    | unify_var (PT(TyRankConstr{Ty=ty,Rank=rk},_)) =
         rank_unify (prank_of ty) rk >> unify_var ty
    | unify_var (PT(UVar (r as ref (SOMEU ty)),_))  = unify_var ty
    | unify_var (ty as PT(UVar (ref (NONEU _)),_))  = return ty
    | unify_var (ty as PT(Vartype _,_))             = return ty
    | unify_var ty = (print ("unify_var fails on " ^ pretype_to_string ty ^ "\n"); fail)
  (* bvar_unify's inputs are reduced to either Vartype or UVar(NONEU),
     and then unified, returning the reduced types *)
  fun bvar_unify (PT(UVar (r as ref (NONEU(kd,rk))),_)) ty2 =
         kind_unify (pkind_of ty2) kd >>
         rank_unify (prank_of ty2) rk >>
         bind (gen_unify c1 c2) r ty2 >>
         unify_var ty2 >- (fn ty2' => return (ty2',ty2'))
    | bvar_unify ty1 (PT(UVar (r as ref (NONEU(kd,rk))),_)) =
         kind_unify (pkind_of ty1) kd >>
         rank_unify (prank_of ty1) rk >>
         bind (gen_unify c1 c2) r ty1 >> 
         unify_var ty1 >- (fn ty1' => return (ty1',ty1'))
    | bvar_unify (ty1 as PT(Vartype (tv1 as (s1,k1,r1)),_))
                 (ty2 as PT(Vartype (tv2 as (s2,k2,r2)),_)) =
         kind_unify k1 k2 >> rank_unify r1 r2 >> return (ty1,ty2)
    | bvar_unify ty1 ty2 =
         unify_var ty1 >- (fn ty1' =>
         unify_var ty2 >- (fn ty2' =>
         bvar_unify ty1' ty2'))
  fun beta_conv_ty_m f ty1 ty2 m =
     let val (ty1',red1) = (top_depth_conv_ty beta_conv_ty ty1, true)
                           handle UNCHANGEDTY => (ty1, false)
         val (ty2',red2) = (top_depth_conv_ty beta_conv_ty ty2, true)
                           handle UNCHANGEDTY => (ty2, false)
     in if red1 orelse red2
        then f ty1' ty2'
        else m
     end
  fun mk_vartype tv = PT(Vartype tv, locn.Loc_None)
  fun shift_context c1 c2 =
        let val theta = map (fn (tv1,tv2) => mk_vartype tv1 |-> mk_vartype tv2) (zip c1 c2)
        in type_subst theta
        end
  fun match_var_type c1 c2 ty1 ty2 =
               (is_uvar_type (the_var_type ty1) handle HOL_ERR _ => false)
        orelse (is_uvar_type (the_var_type ty2) handle HOL_ERR _ => false)
        orelse eq_env c1 c2 ty1 ty2
  fun match_var_types c1 c2 [] [] = true
    | match_var_types c1 c2 (ty1::ty1s) (ty2::ty2s) = match_var_type c1 c2 ty1 ty2 andalso match_var_types c1 c2 ty1s ty2s
    | match_var_types _ _ _ _ = false
  fun vars_of ty = map the_var_type (tyvars e ty)
  fun vars_ofl tys = map the_var_type (foldl (fn (ty,tys) => Lib.union (tyvars e ty) tys) [] tys)
  fun uvars_of ty = filter is_uvar_type (tyvars e ty)
  fun uvars_ofl tys = filter is_uvar_type (foldl (fn (ty,tys) => Lib.union (tyvars e ty) tys) [] tys)
  fun subset s1 s2 = all (fn v => op_mem eq v s2) s1
  fun mk_vs c1 c2 args = map (shift_context c1 c2) args
in
  case (t1, t2) of
    (UVar (r as ref (NONEU(kd,rk))), _) =>
        kind_unify (pkind_of ty2) kd >>
        rank_unify_le (prank_of ty2) (* <= *) rk >>
        bind (gen_unify c1 c2) r (shift_context c2 c1 ty2)
  | (UVar (r as ref (SOMEU ty1)), t2) => gen_unify c1 c2 ty1 ty2
  | (_, UVar _) => gen_unify c2 c1 ty2 ty1
  | (Vartype (tv1 as (s1,k1,r1)), Vartype (tv2 as (s2,k2,r2))) =>
       kind_unify k1 k2 >> rank_unify r1 r2 >>
           (fn e => (if eq_varty c1 c2 tv1 tv2 then ok else fail) e)
  | (Contype {Kind=k1,Rank=r1,...}, Contype {Kind=k2,Rank=r2,...}) =>
       kind_unify k1 k2 >> rank_unify r1 r2 >>
           (fn e => (if eq0 t1 t2 then ok else fail) e)
  | (TyKindConstr{Ty=ty1',Kind=kd1}, _) =>
       kind_unify kd1 (pkind_of ty1') >> gen_unify c1 c2 ty1' ty2 >> return ()
  | (_, TyKindConstr _) => gen_unify c2 c1 ty2 ty1
  | (TyRankConstr{Ty=ty1',Rank=rk1}, _) =>
       rank_unify rk1 (prank_of ty1') >> gen_unify c1 c2 ty1' ty2 >> return ()
  | (_, TyRankConstr _) => gen_unify c2 c1 ty2 ty1
  | (TyApp(ty11, ty12), TyApp(ty21, ty22)) =>
       if is_abs_type (head_ty ty11) then
           gen_unify c1 c2 (head_beta_ty ty1) ty2
       else if is_abs_type (head_ty ty21) then
            gen_unify c1 c2 ty1 (head_beta_ty ty2)
       else
       let val (opr1,args1) = strip_app_type ty1
           val (opr2,args2) = strip_app_type ty2
           val same_opr = length args1 = length args2 andalso eq_env c1 c2 opr1 opr2
           val ho_1 = has_var_type opr1 andalso is_uvar_type(the_var_type opr1)
                                        andalso not same_opr
                                        andalso all has_var_type args1
                                        andalso (not (match_var_types c1 c2 args1 args2)
                                                 orelse (let val uvars_ty2 = uvars_of ty2
                                                             val uvars_args1 = uvars_ofl args1
                                                         in subset uvars_ty2 uvars_args1   (* ??? experimental *)
                                                            andalso subset uvars_args1 uvars_ty2
(*
                                                       (**) andalso (null uvars_args1
                                                                     orelse not (null (intersect uvars_args1
                                                                                                 uvars_ty2)) (**) )
*)
                                                         end))
           val ho_2 = has_var_type opr2 andalso is_uvar_type(the_var_type opr2)
                                        andalso not same_opr
                                        andalso all has_var_type args2
                                        andalso (not (match_var_types c2 c1 args2 args1)
                                                 orelse (let val uvars_ty1 = uvars_of ty1
                                                             val uvars_args2 = uvars_ofl args2
                                                         in subset uvars_ty1 uvars_args2   (* ??? experimental *)
                                                            andalso subset uvars_args2 uvars_ty1
(*
                                                       (**) andalso (null uvars_args2
                                                                     orelse not (null (intersect uvars_args2
                                                                                                 uvars_ty1)) (**) )
*)
                                                         end))
       in
          if ho_1 then
            (* Higher order unification; shift args to other side by abstraction. *)
            let val vs = mk_vs c1 c2 args1
             in if list_eq vs args2
                then gen_unify c1 c2 opr1 opr2
                else gen_unify c1 c2 opr1 (list_mk_abs_type(vs,ty2))
            end
          else if ho_2 then
            (* Higher order unification; shift args to other side by abstraction. *)
            let val vs = mk_vs c2 c1 args2
             in if list_eq vs args1
                then gen_unify c1 c2 opr1 opr2
                else gen_unify c1 c2 (list_mk_abs_type(vs,ty1)) opr2
            end
          else (* normal structural unification *)
            gen_unify c1 c2 ty11 ty21 >> gen_unify c1 c2 ty12 ty22 >> return ()
       end
  | (TyApp(ty11, ty12), _) =>
       if is_abs_type (head_ty ty11) then
           gen_unify c1 c2 (head_beta_ty ty1) ty2
       else
       let val (opr1,args1) = strip_app_type ty1
       in
          if has_var_type opr1 andalso is_uvar_type(the_var_type opr1)
                               andalso all has_var_type args1
          then
            (* Higher order unification; shift args to other side by abstraction. *)
            let val vs = mk_vs c1 c2 args1
             in gen_unify c1 c2 opr1 (list_mk_abs_type(vs,ty2))
            end
          else fail (* normal structural unification *)
       end
  | (_, TyApp(ty21, ty22)) =>
       if is_abs_type (head_ty ty21) then
            gen_unify c1 c2 ty1 (head_beta_ty ty2)
       else
       let val (opr2,args2) = strip_app_type ty2
       in
          if has_var_type opr2 andalso is_uvar_type(the_var_type opr2)
                               andalso all has_var_type args2
          then
            (* Higher order unification; shift args to other side by abstraction. *)
            let val vs = mk_vs c2 c1 args2
             in gen_unify c1 c2 (list_mk_abs_type(vs,ty1)) opr2
            end
          else fail (* normal structural unification *)
       end
  | (TyUniv(ty11, ty12), TyUniv(ty21, ty22)) =>
         bvar_unify ty11 ty21 >- (fn (PT(ty11u,_),PT(ty21u,_)) =>
         case (ty11u,ty21u) of
            (Vartype tv1, Vartype tv2) =>
              gen_unify (tv1::c1) (tv2::c2) ty12 ty22
          | _ => gen_unify c1 c2 ty12 ty22)
  | (TyAbst(ty11, ty12), TyAbst(ty21, ty22)) =>
         bvar_unify ty11 ty21 >- (fn (PT(ty11u,_),PT(ty21u,_)) =>
         case (ty11u,ty21u) of
            (Vartype tv1, Vartype tv2) =>
              gen_unify (tv1::c1) (tv2::c2) ty12 ty22
          | _ => gen_unify c1 c2 ty12 ty22)
  | _ => fail
 end e

val empty_env = ([]:(prekind option ref * prekind option) list,
                 []:(oprerank option ref * oprerank option) list,
                 []:(uvartype ref * uvartype) list)

fun etype_vars e = type_vars

fun unify t1 t2 =
  let val t1' = deep_beta_eta_ty t1
      and t2' = deep_beta_eta_ty t2
      val _ = if not (is_debug()) then () else let
            val ty1s  = pretype_to_string t1
            val ty2s  = pretype_to_string t2
            val ty1s' = pretype_to_string t1'
            val ty2s' = pretype_to_string t2'
         in print (    "unify  " ^ ty1s ^ "\n(beta) " ^ ty1s'
                   ^ "\n   vs. " ^ ty2s ^ "\n(beta) " ^ ty2s' ^ "\n")
         end
  in
  case (gen_unify kind_unify rank_unify rank_unify_le unsafe_bind etype_vars [] [] t1' t2' empty_env)
   of (bindings, SOME ()) => ()
    | (_, NONE) => raise TCERR "unify" "unify failed"
                                    (* ("unify failed: " ^ pretype_to_string t1
                                    ^ "\n      versus: " ^ pretype_to_string t2) *)
  end;

fun can_unify t1 t2 = let
  val ((kind_bindings,rank_bindings,type_bindings), result) =
        gen_unify kind_unify rank_unify rank_unify_le unsafe_bind etype_vars [] [] t1 t2 empty_env
  val _ = app (fn (r, oldvalue) => r := oldvalue) kind_bindings
  val _ = app (fn (r, oldvalue) => r := oldvalue) rank_bindings
  val _ = app (fn (r, oldvalue) => r := oldvalue) type_bindings
in
  isSome result
end

local
     fun (r ref_equiv (PT(value, locn))) (env as (kenv,renv,tenv)) =
       case value of
         UVar (r' as ref (NONEU _)) =>
              r = r' orelse
              let in
                case Lib.assoc1 r' tenv
                 of NONE => false
                  | SOME (_, v) => (r ref_equiv (THEU v)) env
              end
         | UVar (r' as ref (SOMEU t)) => (* r = r' orelse *) (r ref_equiv t) env
           (* equality test unnecessary since r must point to a UVar(NONEU _) *)
         | _ => false

      fun (r ref_occurs_in (PT(value, locn))) (env as (kenv,renv,tenv)) =
        case value
         of UVar (r' as ref (NONEU _)) =>
              r = r' orelse
              let in
                case Lib.assoc1 r' tenv
                 of NONE => false
                  | SOME (_, v) => (r ref_occurs_in (THEU v)) env
              end
          | UVar (r' as ref (SOMEU t)) => (* r = r' orelse *) (r ref_occurs_in t) env
           (* equality test unnecessary since r must point to a UVar(NONEU _) *)
          | TyApp(ty1,ty2) => (r ref_occurs_in ty1) env orelse
                              (r ref_occurs_in ty2) env
          | TyUniv(tyv, ty) => (r ref_occurs_in tyv) env orelse
                               (r ref_occurs_in ty) env
          | TyAbst(tyv, ty) => (r ref_occurs_in tyv) env orelse
                               (r ref_occurs_in ty) env
          | TyKindConstr{Ty,...} => (r ref_occurs_in Ty) env
          | TyRankConstr{Ty,...} => (r ref_occurs_in Ty) env
          | _ => false

      fun kind_unify k1 k2 (env as (kenv,renv,tenv)) =
        let val (kenv', result) = Prekind.safe_unify k1 k2 kenv
        in ((kenv',renv,tenv), result)
        end

      fun rank_unify r1 r2 (env as (kenv,renv,tenv)) =
        let val (renv', result) = Prerank.safe_unify r1 r2 renv
        in ((kenv,renv',tenv), result)
        end

      fun rank_unify_le r1 r2 (env as (kenv,renv,tenv)) =
        let val (renv', result) = Prerank.safe_unify_le r1 r2 renv
        in ((kenv,renv',tenv), result)
        end

in
fun safe_bind unify r value (env as (kenv,renv,tenv)) =
  case Lib.assoc1 r tenv
   of SOME (_, v) => unify (THEU v) value env
    | NONE =>
        if (r ref_equiv value) env then ok env else
        if (r ref_occurs_in value) env then fail env
        else ((kenv,renv,(r, SOMEU value)::tenv), SOME ())

fun safe_unify t1 t2 = gen_unify kind_unify rank_unify rank_unify_le safe_bind deref_type_vars [] [] t1 t2
end


(*---------------------------------------------------------------------------*
 * Passes over a type, turning all of the free type variables not in the     *
 * avoids list into fresh UVars, but doing so consistently by using a pair   *
 * of envs (for bound and free), which are alists from variable names to     *
 * type variable refs.                                                       *
 * Bound variables are not renamed, but are recognized as masking free vars. *
 *---------------------------------------------------------------------------*)


(* in (m1 >>- f), m1 is a monad on kind environments,
    while f is a function that takes a kind and produces
    a monad on a pair of (kind environment, type environment).
    Similarly, in (m2 >>= f), m2 is a monad on rank environments, etc.
*)
infix >>- >>=
fun (m1 >>- f) (env as (rkenv,kdenv,tyenv)) = let
  val (kdenv0, res0) = m1 kdenv
in
  case res0 of
    NONE => ((rkenv,kdenv0,tyenv), NONE)
  | SOME res => f res (rkenv,kdenv0,tyenv)
end

fun (m1 >>= f) (env as (rkenv,kdenv,tyenv)) = let
  val (rkenv0, res0) = m1 rkenv
in
  case res0 of
    NONE => ((rkenv0,kdenv,tyenv), NONE)
  | SOME res => f res (rkenv0,kdenv,tyenv)
end

local
  val rename_kv = Prekind.rename_kv
  val rename_rv = Prerank.rename_rv false
  val rename_rv_new = Prerank.rename_rv true
  fun replace (s,kd,rk) (env as (rkenv,kdenv,tyenv)) =
      case Lib.assoc1 s tyenv of
        NONE => let
          val r = new_uvar(kd,rk)
        in
          ((rkenv,kdenv,(s, r)::tyenv), SOME r)
        end
      | SOME (_, r) => (env, SOME r)
  fun add_bvar (v as PT(Vartype (s,kd,rk), l)) kdavds avds =
          rename_kv kdavds kd >>- (fn kd' =>
          rename_rv rk >>= (fn rk' =>
          let val v' = PT(Vartype (s,kd',rk'), l)
          in return (s::avds, v')
          end))
    | add_bvar (PT(TyKindConstr {Ty,Kind}, _)) kdavds avds =
          rename_kv kdavds Kind >>- (fn Kind' =>
          add_bvar Ty kdavds avds)
    | add_bvar (PT(TyRankConstr {Ty,Rank}, _)) kdavds avds =
          rename_rv Rank >>= (fn Rank' =>
          add_bvar Ty kdavds avds)
    | add_bvar _ _ _ = raise TCERR "rename_typevars" "add_bvar: arg is not variable"
in

fun rename_tv kdavds avds (ty as PT(ty0, locn)) =
  case ty0 of
    Vartype (v as (s,kd,rk)) =>
       rename_kv kdavds kd >>- (fn kd' =>
       rename_rv rk >>= (fn rk' =>
       if mem s avds then return (PT(Vartype(s,kd',rk'), locn)) else replace (s,kd',rk')))
(*
       case Lib.assoc1 s benv
         of SOME _ => return (PT(Vartype(s,kd',rk'), locn))
          | NONE   => replace (s,kd',rk')))
*)
  | Contype {Thy,Tyop,Kind,Rank} =>
       rename_kv kdavds Kind >>- (fn Kind' =>
       rename_rv_new Rank >>= (fn Rank' =>
       return (PT(Contype {Thy=Thy,Tyop=Tyop,Kind=Kind',Rank=Rank'}, locn))))
  | TyApp (ty1, ty2) =>
      rename_tv kdavds avds ty1 >-
      (fn ty1' => rename_tv kdavds avds ty2 >-
      (fn ty2' => return (PT(TyApp(ty1', ty2'), locn))))
  | TyUniv (ty1, ty2) =>
      add_bvar ty1 kdavds avds >- (fn (avds',ty1') =>
      rename_tv kdavds avds' ty2 >-
      (fn ty2' => return (PT(TyUniv(ty1', ty2'), locn))))
  | TyAbst (ty1, ty2) =>
      add_bvar ty1 kdavds avds >- (fn (avds',ty1') =>
      rename_tv kdavds avds' ty2 >-
      (fn ty2' => return (PT(TyAbst(ty1', ty2'), locn))))
  | TyKindConstr {Ty, Kind} =>
      rename_kv kdavds Kind >>- (fn Kind' =>
      rename_tv kdavds avds Ty >- (fn Ty' =>
      return (PT(TyKindConstr {Ty=Ty', Kind=Kind'}, locn))))
  | TyRankConstr {Ty, Rank} =>
      rename_rv Rank >>= (fn Rank' =>
      rename_tv kdavds avds Ty >- (fn Ty' =>
      return (PT(TyRankConstr {Ty=Ty', Rank=Rank'}, locn))))
  | _ (* UVar (ref _) *) => return ty

fun rename_typevars kdavds avds ty = valOf (#2 (rename_tv kdavds avds ty ([],[],[])))
end

fun fromType t =
  if Type.is_var_type t then let
      val (str, kd, rk) = Type.dest_var_type t
    in
      PT(Vartype (str, Prekind.fromKind kd, Prerank.fromRank rk), locn.Loc_None)
    end
  else if Type.is_con_type t then let
      val {Thy, Tyop, Kind, Rank} = dest_thy_con_type t
    in
      PT(Contype {Kind=Prekind.fromKind Kind,
                  Rank=Prerank.fromRank Rank,
                  Thy=Thy, Tyop=Tyop}, locn.Loc_None)
    end
  else if Type.is_app_type t then let
      val (ty1, ty2) = Type.dest_app_type t
    in
      PT(TyApp(fromType ty1, fromType ty2), locn.Loc_None)
    end
  else if Type.is_univ_type t then let
      val (ty1, ty2) = Type.dest_univ_type t
    in
      PT(TyUniv(fromType ty1, fromType ty2), locn.Loc_None)
    end
  else if Type.is_abs_type t then let
      val (ty1, ty2) = Type.dest_abs_type t
    in
      PT(TyAbst(fromType ty1, fromType ty2), locn.Loc_None)
    end
  else raise TCERR "fromType" "Unexpected sort of type"




fun remove_made_links (ty as PT(ty0,locn)) =
  case ty0 of
    UVar(ref (SOMEU ty')) => remove_made_links ty'
  | Vartype(s,kd,rk) => PT(Vartype(s, Prekind.remove_made_links kd,
                                      Prerank.remove_made_links rk), locn)
  | Contype {Thy, Tyop, Kind, Rank} =>
      PT(Contype {Kind=Prekind.remove_made_links Kind, Thy=Thy, Tyop=Tyop,
                  Rank=Prerank.remove_made_links Rank}, locn)
  | TyApp(ty1, ty2) => PT(TyApp (remove_made_links ty1, remove_made_links ty2), locn)
  | TyUniv(tyv, ty) => PT(TyUniv(remove_made_links tyv, remove_made_links ty), locn)
  | TyAbst(tyv, ty) => PT(TyAbst(remove_made_links tyv, remove_made_links ty), locn)
  | TyKindConstr {Ty, Kind} =>
      PT(TyKindConstr {Ty=remove_made_links Ty, Kind=Prekind.remove_made_links Kind}, locn)
  | TyRankConstr {Ty, Rank} =>
      PT(TyRankConstr {Ty=remove_made_links Ty, Rank=Prerank.remove_made_links Rank}, locn)
  | _ => ty

val tyvariant = Lexis.gen_variant Lexis.tyvar_vary

(* needs changing *)
fun generate_new_name r (kd,rk) (kenv, used_so_far) =
  let val result = tyvariant used_so_far "'a"
      val _ = r := SOMEU (PT(Vartype (result,kd,rk), locn.Loc_None))
  in
    ((kenv, result::used_so_far), SOME ())
  end

fun kind_replace_null_links kd (kenv,tenv) =
    let val (kenv', result) = Prekind.replace_null_links kd kenv
    in ((kenv',tenv), result)
    end

(* eta-expansion (see "env" after end below) *is* necessary *)
fun replace_null_links (PT(ty,_)) env = let
in
  case ty of
    UVar (r as ref (NONEU(kd,rk))) => kind_replace_null_links kd >>
                                      generate_new_name r (kd,rk)
  | UVar (ref (SOMEU ty)) => replace_null_links ty
  | TyApp (ty1,ty2) => replace_null_links ty1 >> replace_null_links ty2 >> ok
  | TyUniv (tyv, ty) => replace_null_links tyv >> replace_null_links ty >> ok
  | TyAbst (tyv, ty) => replace_null_links tyv >> replace_null_links ty >> ok
  | TyKindConstr {Ty,Kind} => replace_null_links Ty >> kind_replace_null_links Kind >> ok
  | TyRankConstr {Ty,Rank} => replace_null_links Ty >> ok
  | Vartype (s,kd,rk) => kind_replace_null_links kd
  | Contype {Thy,Tyop,Kind,Rank} => kind_replace_null_links Kind
end env

fun clean (pty as PT(ty, locn)) =
(
  case ty of
    Vartype (s,kd,rk) => Type.mk_var_type (s, Prekind.toKind kd, Prerank.toRank rk)
  | Contype {Thy,Tyop,Kind,Rank} => Type.mk_thy_con_type {Thy=Thy, Tyop=Tyop,
                                         Kind=Prekind.toKind Kind, Rank=Prerank.toRank Rank}
  | TyApp(ty1,ty2)  => (Type.mk_app_type  (clean ty1, clean ty2)
                          handle Feedback.HOL_ERR e =>
                            ((*print ("Applying " ^ type_to_string (clean ty1)
                                    ^ " to " ^ type_to_string (clean ty2) ^ "\n");*)
                             raise Feedback.mk_HOL_ERR "Pretype" "clean" (#message e)))
  | TyUniv (tyv,ty) => Type.mk_univ_type (clean tyv, clean ty)
  | TyAbst (tyv,ty) => Type.mk_abs_type  (clean tyv, clean ty)
  | TyKindConstr {Ty,Kind} => clean Ty
  | TyRankConstr {Ty,Rank} => clean Ty
  | _ => raise Fail "Don't expect to see links remaining at this stage of type inference"
) handle e => raise (wrap_exn "Pretype.clean" (pretype_to_string pty) e)

fun toType ty =
  let val ty = if do_beta_conv_types()
                      then deep_beta_eta_ty ty
                      else ty
      val _ = replace_null_links ty (kindvars ty, tyvars ty)
  in
    clean (remove_made_links ty)
  end
  handle e => raise (wrap_exn "Pretype" "toType" e)


val fun_tyc0 = Contype{Tyop = "fun", Thy = "min",
                       Kind = Prekind.mk_arity 2, Rank = Prerank.Zerorank}

(* chase returns the effective range of an effective function type *)

fun chase ty =
  let val (dom,rng) = dom_rng ty
                      handle HOL_ERR _ => dom_rng (deep_beta_eta_ty ty)
  in rng
  end
  handle HOL_ERR _ => raise Fail ("chase applied to non-function type: " ^ pretype_to_string ty)

(*
local
fun CERR ty = Fail ("chase applied to non-function type: " ^ pretype_to_string ty)
in
fun chase (ty as PT(TyApp(PT(TyApp(PT(tyc, _), _), _), ty1), _)) =
    if eq0 tyc fun_tyc0 then ty1 else raise CERR ty
  | chase (ty as PT(TyApp(PT(TyAbst(_, _), _), _), _)) =
    (chase (beta_conv_ty ty) handle _ => raise CERR ty)
  | chase (PT(TyKindConstr{Ty,Kind}, _)) = chase Ty
  | chase (PT(TyRankConstr{Ty,Rank}, _)) = chase Ty
  | chase (PT(UVar(ref (SOMEU ty)), _)) = chase ty
  | chase (ty as PT(UVar(r as ref (NONEU(kd,rk))), _)) =
    if kd <> Prekind.typ then raise CERR ty
    else let
        val typ = Prekind.typ
        val ty1 = new_uvar(typ,rk);
        val ty2 = new_uvar(typ,rk);
        val ty' = ty1 --> ty2
     in r := SOMEU ty';
        ty2
    end
  | chase ty = raise CERR ty
end
*)


(*---------------------------------------------------------------------------
 * Kind inference for HOL types. Looks ugly because of error messages, but is
 * actually very simple, given side-effecting unification.
 *---------------------------------------------------------------------------*)

fun is_atom0 (Vartype _) = true
  | is_atom0 (Contype _) = true
  | is_atom0 (TyKindConstr{Ty,...}) = is_atom Ty
  | is_atom0 (TyRankConstr{Ty,...}) = is_atom Ty
  | is_atom0 (UVar (r as ref (NONEU _))) = false
  | is_atom0 (UVar (r as ref (SOMEU ty))) = is_atom ty
  | is_atom0 ty = false
and is_atom (PT(pty,locn)) = is_atom0 pty



local
  fun default_kdprinter x = "<kind>"
  fun default_typrinter x = "<hol_type>"
  fun Locn (PT(_,locn)) = locn
in
fun KC printers = let
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
  fun check(PT(TyApp(opr,arg),locn)) =
      (check opr;
       check arg;
       Prekind.unify (pkind_of opr)
       (pkind_of arg ==> Prekind.new_uvar())
       handle (e as Feedback.HOL_ERR{origin_structure="Prekind",
                                     origin_function="unify",message})
       => let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 2
              val opr' = toType opr
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val arg' = toType arg
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val message =
                  String.concat
                      [
                       "\nKind inference failure: unable to infer a kind \
                       \for the application of\n\n",
                       pty opr',
                       "\n\n"^locn.toString (Locn opr)^"\n\n",
                       if (is_atom opr) then ""
                       else ("which has kind\n\n" ^
                             pkd(Type.kind_of opr') ^ "\n\n"),

                       "to\n\n",
                       pty arg',
                       "\n\n"^locn.toString (Locn arg)^"\n\n",

                       if (is_atom arg) then ""
                       else ("which has kind\n\n" ^
                             pkd(Type.kind_of arg') ^ "\n\n"),

                       "kind unification failure message: ", message, "\n"]
          in
            Feedback.set_trace "kinds" tmp;
            kcheck_say message;
            last_kcerror := SOME (TyAppFail(opr',arg'), Locn arg);
            raise ERRloc"kindcheck" (Locn opr (* arbitrary *)) "failed"
          end)
    | check (PT(TyUniv(Bvar, Body), locn)) =
       (check Bvar; check Body; Prekind.unify (pkind_of Body) Prekind.typ
       handle (e as Feedback.HOL_ERR{origin_structure="Prekind",
                                     origin_function="unify",message})
       => let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 2
              val real_type = toType Body
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val real_kind = Prekind.toKind Prekind.typ
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val message =
                  String.concat
                      [
                       "\nKind inference failure: the type\n\n",
                       pty real_type,
                       "\n\n"^locn.toString (Locn Body)^"\n\n",
                       if (is_atom Body) then ""
                       else ("which has kind\n\n" ^
                             pkd(Type.kind_of real_type) ^ "\n\n"),

                       "can not be constrained to be of kind\n\n",
                       pkd real_kind,

                       "kind unification failure message: ", message, "\n"]
          in
            Feedback.set_trace "kinds" tmp;
            kcheck_say message;
            last_kcerror := SOME (TyUnivFail(real_type), Locn Body);
            raise ERRloc "kindcheck" locn "failed"
          end)
    | check (PT(TyAbst(Bvar, Body), Locn)) = (check Bvar; check Body)
    | check (PT(TyKindConstr{Ty,Kind},locn)) =
       (check Ty; Prekind.unify (pkind_of Ty) Kind
       handle (e as Feedback.HOL_ERR{origin_structure="Prekind",
                                     origin_function="unify",message})
       => let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 2
              val real_type = toType Ty
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val Prekind.PK(_,kd_locn) = Kind
              val real_kind = Prekind.toKind Kind
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val message =
                  String.concat
                      [
                       "\nKind inference failure: the type\n\n",
                       pty real_type,
                       "\n\n"^locn.toString (Locn Ty)^"\n\n",
                       if (is_atom Ty) then ""
                       else ("which has kind\n\n" ^
                             pkd(Type.kind_of real_type) ^ "\n\n"),

                       "can not be constrained to be of kind\n\n",
                       pkd real_kind,
                       "\n\n"^locn.toString kd_locn^"\n\n",

                       "kind unification failure message: ", message, "\n"]
          in
            Feedback.set_trace "kinds" tmp;
            kcheck_say message;
            last_kcerror := SOME (TyKindConstrFail(real_type, real_kind), kd_locn);
            raise ERRloc "kindcheck" locn "failed"
          end)
    | check (PT(TyRankConstr{Ty,Rank},locn)) =
       (check Ty; Prerank.unify (prank_of Ty) Rank
       handle (e as Feedback.HOL_ERR{origin_structure="Prerank",
                                     origin_function="unify",message})
       => let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 2
              val real_type = toType Ty
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val real_rank = Prerank.toRank Rank
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val message =
                  String.concat
                      [
                       "\nRank inference failure: the type\n\n",
                       pty real_type,
                       "\n\n"^locn.toString (Locn Ty)^"\n\n",
                       if (is_atom Ty) then ""
                       else ("which has rank " ^
                             prk(Type.rank_of real_type) ^ "\n\n"),

                       "can not be constrained to be of rank ",
                       prk real_rank, "\n\n",

                       "rank unification failure message: ", message, "\n"]
          in
            Feedback.set_trace "kinds" tmp;
            kcheck_say message;
            last_kcerror := SOME (TyRankConstrFail(real_type, real_rank), locn);
            raise ERRloc "rankcheck" locn "failed"
          end
       | (e as Feedback.HOL_ERR{origin_structure="Prerank",
                                     origin_function="unify_le",message})
       => let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 2
              val real_type = toType Ty
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val real_rank = Prerank.toRank Rank
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val message =
                  String.concat
                      [
                       "\nRank inference failure: the type\n\n",
                       pty real_type,
                       "\n\n"^locn.toString (Locn Ty)^"\n\n",
                       if (is_atom Ty) then ""
                       else ("which has rank " ^
                             prk(Type.rank_of real_type) ^ "\n\n"),

                       "can not be constrained to be <= rank ",
                       prk real_rank, "\n\n",

                       "rank unification failure message: ", message, "\n"]
          in
            Feedback.set_trace "kinds" tmp;
            kcheck_say message;
            last_kcerror := SOME (TyRankLEConstrFail(real_type, real_rank), locn);
            raise ERRloc "rankcheck" locn "failed"
          end)
    | check _ = ()
in check
end end;

val checkkind = KC

fun kindcheck pfns pty0 = let
  val _ = KC pfns pty0
in
  toType pty0
end

local
  fun mk_not_univ_type ty =
       let val (bvars,body) = strip_univ_type ty
           val bvars0 = map the_var_type bvars
           val args = map (fn bvar => new_uvar(pkind_of bvar,prank_of bvar)) bvars
           val theta = map (op |->) (zip bvars0 args)
           val body' = type_subst theta body
       in body'
       end
  fun reconcile p t =
      (*if eq p t then p
      else*)
      if is_univ_type p andalso is_not_univ_type t
      then reconcile (mk_not_univ_type p) t
      else if is_app_type p andalso is_app_type t then let
          val (opr1,arg1) = dest_app_type p
          val (opr2,arg2) = dest_app_type t
        in mk_app_type(reconcile opr1 opr2, reconcile arg1 arg2)
        end
      else if is_univ_type p andalso is_univ_type t then let
          val (bvar1,body1) = dest_univ_type p
          val (bvar2,body2) = dest_univ_type t
        in mk_univ_type(bvar1, reconcile body1 body2)
        end
      else if is_abs_type p andalso is_abs_type t then let
          val (bvar1,body1) = dest_abs_type p
          val (bvar2,body2) = dest_abs_type t
        in mk_abs_type(bvar1, reconcile body1 body2)
        end
      else p
in
fun reconcile_univ_types pat targ =
    let val pty = reconcile (deep_beta_eta_ty pat) (deep_beta_eta_ty targ)
        val _ = KC NONE pty
    in pty
    end
end

fun remove_ty_aq t =
  if parse_type.is_ty_antiq t then parse_type.dest_ty_antiq t
  else raise mk_HOL_ERR "Parse" "type parser" "antiquotation is not of a type"

(* "qtyop" refers to "qualified" type operator, i.e., qualified by theory name. *)

fun mk_conty{Thy,Tyop,Kind,Rank,Locn} =
  PT(Contype {Thy=Thy, Tyop=Tyop, Kind=Kind, Rank=Rank}, Locn)

fun do_qtyop {Thy,Tyop,Locn,Args} =
  List.foldl (fn (arg,acc) => PT(TyApp(acc,arg),Locn))
             (mk_conty{Thy=Thy,Tyop=Tyop,Kind=Prekind.mk_arity(length Args),Rank=Prerank.Zerorank,Locn=Locn})
             Args

fun tyop_to_qtyop ((tyop,locn), args) =
  case Type.decls tyop of
    [] => raise mk_HOL_ERRloc "Parse" "type parser" locn
                              (tyop^" not a known type operator")
  | {Thy,Tyop} :: _ => do_qtyop {Thy = Thy, Tyop = Tyop, Locn = locn, Args = args}

fun do_kindcast {Ty,Kind,Locn} =
  PT(TyKindConstr {Ty=Ty,Kind=Kind}, Locn)

fun do_rankcast {Ty,Rank,Locn} =
  PT(TyRankConstr {Ty=Ty,Rank=Rank}, Locn)

fun mk_basevarty((s,kd,rk),locn) = PT(Vartype(s,kd,rk), locn)

val termantiq_constructors =
    {vartype = mk_basevarty, qtyop = do_qtyop,
     tyop = tyop_to_qtyop,
     antiq = fn x => fromType (remove_ty_aq x),
     kindcast = do_kindcast, rankcast = do_rankcast,
     tycon = mk_conty, tyapp = mk_app_type,
     tyuniv = mk_univ_type, tyabs = mk_abs_type}

val typantiq_constructors =
    {vartype = mk_basevarty, qtyop = do_qtyop,
     tyop = tyop_to_qtyop,
     antiq = fromType,
     kindcast = do_kindcast, rankcast = do_rankcast,
     tycon = mk_conty, tyapp = mk_app_type,
     tyuniv = mk_univ_type, tyabs = mk_abs_type}

end;
