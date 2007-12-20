structure Pretype :> Pretype =
struct

open HolKernel optmonad;
infix >> >-;

  type prekind = Prekind.prekind
  type prerank = Prerank.prerank
  type kind = Kind.kind
  type hol_type = Type.hol_type
  type pretyvar = string * prekind * prerank
  type tyvar = Type.tyvar

val TCERR = mk_HOL_ERR "Pretype";
val ERRloc = mk_HOL_ERRloc "Pretype"

 datatype pretype0
    = Vartype of pretyvar
    | Contype of {Thy : string, Tyop : string, Kind : prekind, Rank : prerank}
    | TyApp  of pretype * pretype
    | TyUniv of pretype * pretype
    | TyAbst of pretype * pretype
    | TyKindConstr of {Ty : pretype, Kind : prekind}
    | TyRankConstr of {Ty : pretype, Rank : prerank}
    | UVar of pretype option ref
 and pretype = PT of pretype0 locn.located

fun tylocn (PT(_,locn)) = locn

(*---------------------------------------------------------------------------
  Location-ignoring but alpha-equivalence respecting equality for pretypes.
 ---------------------------------------------------------------------------*)

val eq_kind = Prekind.eq
val eq_rank = Prerank.eq

fun eq_tyvar (s,kd,rk) (s',kd',rk') = s=s' andalso eq_kind kd kd' andalso eq_rank rk rk'

fun Vartype_of0 (Vartype v) = v
  | Vartype_of0 (TyKindConstr{Ty=ty, Kind=kd}) = Vartype_of ty
  | Vartype_of0 (TyRankConstr{Ty=ty, Rank=rk}) = Vartype_of ty
  | Vartype_of0 _ = raise TCERR "Vartype_of" "not a variable or a kind or rank constraint"
and Vartype_of (PT(ty,locn)) = Vartype_of0 ty;

fun eq_varty   []      []    v v' = eq_tyvar v v'
  | eq_varty (x::xs) (y::ys) v v' =
      (eq_tyvar x v andalso eq_tyvar y v') orelse eq_varty xs ys v v'
  | eq_varty   _       _     _ _  = false

fun eq_env0 e1 e2 (Vartype v)                (Vartype v')              = eq_varty e1 e2 v v'
  | eq_env0 e1 e2 (Contype{Tyop=Tyop, Thy=Thy, Kind=Kind, Rank=Rank })
                  (Contype{Tyop=Tyop',Thy=Thy',Kind=Kind',Rank=Rank'}) = Tyop=Tyop' andalso Thy=Thy' andalso
                                                                         eq_kind Kind Kind' andalso eq_rank Rank Rank'
  | eq_env0 e1 e2 (TyApp(ty1,ty2))           (TyApp(ty1',ty2'))        = eq_env e1 e2 ty1 ty1' andalso eq_env e1 e2 ty2 ty2'
  | eq_env0 e1 e2 (TyUniv(ty1,ty2))          (TyUniv(ty1',ty2'))       =
          eq_env (Vartype_of ty1::e1) (Vartype_of ty1'::e2) ty2 ty2'
  | eq_env0 e1 e2 (TyAbst(ty1,ty2))          (TyAbst(ty1',ty2'))       =
          eq_env (Vartype_of ty1::e1) (Vartype_of ty1'::e2) ty2 ty2'
  | eq_env0 e1 e2 (TyKindConstr{Ty=ty, Kind=kd })
                  (TyKindConstr{Ty=ty',Kind=kd'})                      = eq_env e1 e2 ty ty' andalso eq_kind kd kd'
  | eq_env0 e1 e2 (TyRankConstr{Ty=ty, Rank=rk })
                  (TyRankConstr{Ty=ty',Rank=rk'})                      = eq_env e1 e2 ty ty' andalso eq_rank rk rk'
  | eq_env0 e1 e2 (UVar (r as ref NONE))     (UVar (r' as ref NONE))   = r=r'
  | eq_env0 e1 e2 (UVar (ref (SOME ty)))     (UVar (ref (SOME ty')))   = eq_env e1 e2 ty ty'
  | eq_env0 e1 e2 _                          _                         = false
and eq_env  e1 e2 (PT (value,locn))          (PT (value',locn'))       = eq_env0 e1 e2 value value'

val eq0 = eq_env0 [] []
and eq  = eq_env  [] [];

(*
fun eq0 (Vartype v)                (Vartype v')              = eq_tyvar v v'
  | eq0 (Contype{Tyop=Tyop, Thy=Thy, Kind=Kind, Rank=Rank })
        (Contype{Tyop=Tyop',Thy=Thy',Kind=Kind',Rank=Rank'}) = Tyop=Tyop' andalso Thy=Thy' andalso
                                                                 eq_kind Kind Kind' andalso eq_rank Rank Rank'
  | eq0 (TyApp(ty1,ty2))           (TyApp(ty1',ty2'))        = eq ty1 ty1' andalso eq ty2 ty2'
  | eq0 (TyUniv(ty1,ty2))          (TyUniv(ty1',ty2'))       = eq ty1 ty1' andalso eq ty2 ty2'
  | eq0 (TyAbst(ty1,ty2))          (TyAbst(ty1',ty2'))       = eq ty1 ty1' andalso eq ty2 ty2'
  | eq0 (TyKindConstr{Ty=ty, Kind=kd})
        (TyKindConstr{Ty=ty',Kind=kd'})                      = eq ty ty' andalso eq_kind kd kd'
  | eq0 (TyRankConstr{Ty=ty, Rank=rk })
        (TyRankConstr{Ty=ty',Rank=rk'})                      = eq ty ty' andalso eq_rank Rank Rank'
  | eq0 (UVar (r as ref NONE))     (UVar (r' as ref NONE))   = r=r'
  | eq0 (UVar (ref (SOME ty)))     (UVar (ref (SOME ty')))   = eq ty ty'
  | eq0 _                          _                         = false
and eq  (PT (value,locn))          (PT (value',locn'))       = eq0 value value'
*)

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
    | (UVar (ref NONE), UVar (ref(SOME _))) => LESS
    | (UVar (ref NONE), UVar (ref NONE)) => EQUAL
    | (UVar (ref NONE), _)               => GREATER
    | (UVar (ref(SOME ty1)), UVar (ref(SOME ty2))) => compare(ty1,ty2)
    | (UVar (ref(SOME _)), _)            => GREATER
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

fun mk_app_type(ty1 as PT(_,loc1), ty2 as PT(_,loc2)) =
    PT(TyApp(ty1,ty2), locn.between loc1 loc2)

fun dest_app_type(PT(UVar(ref(SOME ty)),loc)) = dest_app_type ty
  | dest_app_type(ty as PT(TyApp(ty1,ty2),loc)) = (ty1,ty2)
  | dest_app_type _ = raise TCERR "dest_app_type" "not a type application";

fun mk_univ_type(ty1 as PT(_,loc1), ty2 as PT(_,loc2)) =
    PT(TyUniv(ty1,ty2), locn.between loc1 loc2)

fun dest_univ_type(PT(UVar(ref(SOME ty)),loc)) = dest_univ_type ty
  | dest_univ_type(ty as PT(TyUniv(ty1,ty2),loc)) = (ty1,ty2)
  | dest_univ_type _ = raise TCERR "dest_univ_type" "not a universal type";

fun mk_abs_type(ty1 as PT(_,loc1), ty2 as PT(_,loc2)) =
    PT(TyAbst(ty1,ty2), locn.between loc1 loc2)

fun dest_abs_type(PT(UVar(ref(SOME ty)),loc)) = dest_abs_type ty
  | dest_abs_type(ty as PT(TyAbst(ty1,ty2),loc)) = (ty1,ty2)
  | dest_abs_type _ = raise TCERR "dest_abs_type" "not a type abstraction";

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
  | UVar (ref NONE) => []
  | UVar (ref (SOME ty')) => kindvars ty'

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
  | UVar (ref NONE) => []
  | UVar (ref (SOME ty')) => tyvars ty'

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

fun new_uvar () = PT (UVar(ref NONE), locn.Loc_None)

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
  | UVar (r' as ref NONE) => r = r'
  | UVar (r' as ref (SOME t)) => r = r' orelse r ref_occurs_in t

infix ref_equiv
fun r ref_equiv (PT(value, locn)) =
  case value of
    UVar (r' as ref NONE) => r = r'
  | UVar (r' as ref (SOME t)) => r = r' orelse r ref_equiv t
  | _ => false

  fun has_free_uvar_kind (PT(pty,_)) =
    case pty of
      UVar (ref NONE)        => false
    | UVar (ref (SOME pty')) => has_free_uvar_kind pty'
    | Vartype (_,kd,_)       => Prekind.has_free_uvar kd
    | Contype {Kind,...}     => Prekind.has_free_uvar Kind
    | TyApp(ty1, ty2)        => has_free_uvar_kind ty1 orelse has_free_uvar_kind ty2
    | TyAbst(tyv, ty)        => has_free_uvar_kind tyv orelse has_free_uvar_kind ty
    | TyUniv(tyv, ty)        => has_free_uvar_kind tyv orelse has_free_uvar_kind ty
    | TyKindConstr {Ty, Kind} => has_free_uvar_kind Ty orelse Prekind.has_free_uvar Kind
    | TyRankConstr {Ty, Rank} => has_free_uvar_kind Ty

  fun has_free_uvar (PT(pty,_)) =
    case pty of
      UVar (ref NONE)        => true
    | UVar (ref (SOME pty')) => has_free_uvar pty'
    | Vartype _              => false
    | Contype _              => false
    | TyApp(ty1, ty2)        => has_free_uvar ty1 orelse has_free_uvar ty2
    | TyAbst(tyv, ty)        => has_free_uvar tyv orelse has_free_uvar ty
    | TyUniv(tyv, ty)        => has_free_uvar tyv orelse has_free_uvar ty
    | TyKindConstr {Ty, ...} => has_free_uvar Ty
    | TyRankConstr {Ty, ...} => has_free_uvar Ty


(*
fun kind_bind f r value (kd_env,ty_env) =
  let val (kd_env', result) = Prekind.safe_bind f r value kd_env
  in ((kd_env',ty_env), result)
  end
*)

fun kind_unify k1 k2 (kd_env,rk_env,ty_env) =
  let val (kd_env', result) = Prekind.unsafe_unify k1 k2 kd_env
  in ((kd_env',rk_env,ty_env), result)
  end

fun rank_unify r1 r2 (kd_env,rk_env,ty_env) =
  let val (rk_env', result) = Prerank.unsafe_unify r1 r2 rk_env
  in ((kd_env,rk_env',ty_env), result)
  end

fun unsafe_bind f r value =
  if r ref_equiv value
  then ok
  else if r ref_occurs_in value orelse isSome (!r)
       then fail
    else (fn (kd_env,rk_env,acc) =>
             (((kd_env,rk_env,(r, !r)::acc), SOME ()) before r := SOME value))


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
fun gen_unify (kind_unify:prekind -> prekind -> ('a -> 'a * unit option))
              (rank_unify:prerank -> prerank -> ('a -> 'a * unit option))
              bind (ty1 as PT(t1,locn1)) (ty2 as PT(t2,locn2)) e = let
  val gen_unify = gen_unify kind_unify rank_unify bind
in
  case (t1, t2) of
    (UVar (r as ref NONE), _) => bind gen_unify r ty2
  | (UVar (r as ref (SOME t1)), t2) => gen_unify t1 ty2
  | (_, UVar _) => gen_unify ty2 ty1
  | (Vartype (tv1 as (s1,k1,r1)), Vartype (tv2 as (s2,k2,r2))) =>
       kind_unify k1 k2 >> rank_unify r1 r2 >>
           (fn e => (if eq_tyvar tv1 tv2 then ok else fail) e)
  | (Contype {Kind=k1,Rank=r1,...}, Contype {Kind=k2,Rank=r2,...}) =>
       kind_unify k1 k2 >> rank_unify r1 r2 >>
           (fn e => (if eq0 t1 t2 then ok else fail) e)
  | (TyApp(ty11, ty12), TyApp(ty21, ty22)) =>
       gen_unify ty11 ty21 >> gen_unify ty12 ty22 >> return ()
  | (TyUniv(ty11, ty12), TyUniv(ty21, ty22)) =>
       gen_unify ty11 ty21 >> gen_unify ty12 ty22 >> return ()
  | (TyAbst(ty11, ty12), TyAbst(ty21, ty22)) =>
       gen_unify ty11 ty21 >> gen_unify ty12 ty22 >> return ()
  | (TyKindConstr{Ty=ty1,Kind=kd1}, TyKindConstr{Ty=ty2,Kind=kd2}) =>
       kind_unify kd1 kd2 >> gen_unify ty1 ty2 >> return ()
  | (TyRankConstr{Ty=ty1,Rank=rk1}, TyRankConstr{Ty=ty2,Rank=rk2}) =>
       rank_unify rk1 rk2 >> gen_unify ty1 ty2 >> return ()
  | _ => fail
 end e

val empty_env = ([]:(prekind option ref * prekind option) list,
                 []:(prerank option ref * prerank option) list,
                 []:(pretype option ref * pretype option) list)

fun unify t1 t2 =
  case (gen_unify kind_unify rank_unify unsafe_bind t1 t2 empty_env)
   of (bindings, SOME ()) => ()
    | (_, NONE) => raise TCERR "unify" "unify failed";

fun can_unify t1 t2 = let
  val ((kind_bindings,rank_bindings,type_bindings), result) =
        gen_unify kind_unify rank_unify unsafe_bind t1 t2 empty_env
  val _ = app (fn (r, oldvalue) => r := oldvalue) kind_bindings
  val _ = app (fn (r, oldvalue) => r := oldvalue) rank_bindings
  val _ = app (fn (r, oldvalue) => r := oldvalue) type_bindings
in
  isSome result
end

local
  fun (r ref_equiv (PT(value, locn))) (env as (kenv,renv,tenv)) =
       case value of
         UVar (r' as ref NONE) =>
              r = r' orelse
              let in
                case Lib.assoc1 r' tenv
                 of NONE => false
                  | SOME (_, v) => (r ref_equiv v) env
              end
         | UVar (ref (SOME t)) => (r ref_equiv t) env
         | _ => false

      fun (r ref_occurs_in (PT(value, locn))) (env as (kenv,renv,tenv)) =
        case value
         of UVar (r' as ref NONE) =>
              r = r' orelse
              let in
                case Lib.assoc1 r' tenv
                 of NONE => false
                  | SOME (_, v) => (r ref_occurs_in v) env
              end
          | UVar (ref (SOME t)) => (r ref_occurs_in t) env
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

in
fun safe_bind unify r value (env as (kenv,renv,tenv)) =
  case Lib.assoc1 r tenv
   of SOME (_, v) => unify v value env
    | NONE =>
        if (r ref_equiv value) env then ok env else
        if (r ref_occurs_in value) env then fail env
        else ((kenv,renv,(r,value)::tenv), SOME ())

fun safe_unify t1 t2 = gen_unify kind_unify rank_unify safe_bind t1 t2
end


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
  | UVar (ref (SOME t)) => apply_subst subst t
  | UVar (r as ref NONE) =>
      case (Lib.assoc1 r subst) of
        NONE => pt
      | SOME (_, value) => apply_subst subst value


val op ==> = Prekind.==>
fun pkind_of0 (Vartype(s,kd,rk)) = kd
  | pkind_of0 (Contype{Kind, ...}) = Kind
  | pkind_of0 (TyApp(opr,arg)) = Prekind.chase (pkind_of opr)
  | pkind_of0 (TyUniv _) = Prekind.typ
  | pkind_of0 (TyAbst(Bvar,Body)) = pkind_of Bvar ==> pkind_of Body
  | pkind_of0 (TyKindConstr{Ty,Kind}) = Kind
  | pkind_of0 (TyRankConstr{Ty,Rank}) = pkind_of Ty
  | pkind_of0 (UVar (r as ref NONE)) = Prekind.new_uvar() (* a guess *)
  | pkind_of0 (UVar (r as ref (SOME ty))) = pkind_of ty
and pkind_of (PT(ty,locn)) = pkind_of0 ty

local
val zero = Prerank.Zerorank
val inc  = Prerank.Sucrank
val max  = Prerank.Maxrank
in
fun prank_of0 (Vartype(s,kd,rk)) = rk
  | prank_of0 (Contype{Rank, ...}) = Rank
  | prank_of0 (TyApp(opr,arg))     = max(prank_of opr,       prank_of arg)
  | prank_of0 (TyUniv(Bvar,Body))  = max(inc(prank_of Bvar), prank_of Body)
  | prank_of0 (TyAbst(Bvar,Body))  = max(prank_of Bvar,      prank_of Body)
  | prank_of0 (TyKindConstr{Ty,Kind}) = prank_of Ty
  | prank_of0 (TyRankConstr{Ty,Rank}) = Rank
  | prank_of0 (UVar (r as ref NONE)) = zero (* a guess *)
  | prank_of0 (UVar (r as ref (SOME ty))) = prank_of ty
and prank_of (PT(ty,locn)) = prank_of0 ty
end;


(*---------------------------------------------------------------------------*
 * The free type variables in a pretype.  Tail recursive (from Ken Larsen).     *
 *---------------------------------------------------------------------------*)

local fun TV (v as PT(Vartype _,_)) B A k = if mem v B then k A
                                            else k (Lib.insert v A)
        | TV (PT(Contype _,_)) B A k      = k A
        | TV (PT(TyApp(opr, ty),_)) B A k = TV opr B A (fn q => TV ty B q k)
        | TV (PT(TyUniv(v,ty),_)) B A k   = TV ty (Lib.insert v B) A k
        | TV (PT(TyAbst(v,ty),_)) B A k   = TV ty (Lib.insert v B) A k
        | TV (PT(TyKindConstr{Ty,Kind},_)) B A k = TV Ty B A k
        | TV (PT(TyRankConstr{Ty,Rank},_)) B A k = TV Ty B A k
        | TV (PT(UVar(ref NONE),_)) B A k = k A
        | TV (PT(UVar(ref(SOME ty)),_)) B A k = TV ty B A k
      and TVl (ty::tys) B A k             = TV ty B A (fn q => TVl tys B q k)
        | TVl _ B A k = k A
in
fun type_vars ty = rev(TV ty [] [] Lib.I)
fun type_varsl L = rev(TVl L [] [] Lib.I)
end;

fun type_vars_subst (theta : (pretype,pretype)Lib.subst) = type_varsl (map #residue theta);

(*---------------------------------------------------------------------------*
 * Given a type variable and a list of type variables, if the type variable  *
 * does not exist on the list, then return the type variable. Otherwise,     *
 * rename the type variable and try again. Note well that the variant uses   *
 * only the name of the variable as a basis for testing equality. Experience *
 * has shown that basing the comparison on all of the name, the arity, the   *
 * rank, and the type arguments of the variable resulted in needlessly       *
 * confusing formulas occasionally being displayed in interactive sessions.  *
 *---------------------------------------------------------------------------*)

fun gen_variant P caller =
  let fun var_name (PT(Vartype(Name,_,_),_)) = Name
        | var_name _ = raise ERR caller "not a variable"
      fun vary vlist (PT(Vartype(Name,Kind,Rank),locn)) =
          let val L = map var_name vlist
              val next = Lexis.gen_variant Lexis.tyvar_vary L
              fun loop name =
                 let val s = next name
                 in if P s then loop s else s
                 end
          in PT(Vartype(loop Name, Kind, Rank),locn)
          end
        | vary _ _ = raise ERR caller "2nd argument should be a variable"
  in vary
  end;

val variant_type       = gen_variant (K false) "variant_type";

(*---------------------------------------------------------------------------*
 *    Replace arbitrary subpretypes in a pretype. Renaming.                  *
 *---------------------------------------------------------------------------*)

val emptysubst:(pretype,pretype)Binarymap.dict = Binarymap.mkDict compare
local
  open Binarymap
  val toRank = Prerank.toRank
  fun addb [] A = A
    | addb ({redex,residue}::t) (A,b) =
      addb t (if toRank(prank_of redex) >= toRank(prank_of residue)
              then (insert(A,redex,residue),
                    is_var_type redex andalso b)
              else raise ERR "type_subst" "redex has lower rank than residue")
  fun unloc_of (PT(ty,loc)) = ty
in
fun type_subst [] = I
  | type_subst theta =
    let val frees = type_vars_subst theta
        val (fmap,b) = addb theta (emptysubst, true)
        fun vsubs0 fmap (v as Vartype _) =
               (case peek(fmap,PT(v, locn.Loc_None)) of
                                     NONE => v
                                   | SOME (PT(y,_)) => y)
          | vsubs0 fmap (TyApp(opr,ty)) = TyApp(vsubs fmap opr, vsubs fmap ty)
          | vsubs0 fmap (TyUniv(Bvar,Body)) =
               let val fvs = Lib.subtract (type_vars Body) [Bvar]
                   val Bvar' = variant_type (Lib.union frees fvs) Bvar
               in if eq Bvar Bvar' then TyUniv(Bvar, vsubs fmap Body)
                  else TyUniv(Bvar', vsubs (insert(fmap,Bvar,Bvar')) Body)
               end
          | vsubs0 fmap (TyAbst(Bvar,Body)) =
               let val fvs = Lib.subtract (type_vars Body) [Bvar]
                   val Bvar' = variant_type (Lib.union frees fvs) Bvar
               in if eq Bvar Bvar' then TyAbst(Bvar, vsubs fmap Body)
                  else TyAbst(Bvar', vsubs (insert(fmap,Bvar,Bvar')) Body)
               end
          | vsubs0 fmap (TyKindConstr{Ty,Kind}) =
                         TyKindConstr{Ty=vsubs fmap Ty,Kind=Kind}
          | vsubs0 fmap (TyRankConstr{Ty,Rank}) =
                         TyRankConstr{Ty=vsubs fmap Ty,Rank=Rank}
          | vsubs0 fmap (UVar (r as ref(SOME ty))) = unloc_of (vsubs fmap ty)
          | vsubs0 fmap t = t
        and vsubs fmap (PT(ty,locn)) = PT(vsubs0 fmap ty,locn)
(*
        fun subs ty =
          case peek(fmap,ty)
           of SOME residue => residue
            | NONE =>
              (case ty
                of TyApp(opr,ty) => TyApp(subs opr, subs ty)
                 | TyAll(Bvar,Body) => TyAll(Bvar,subs Body)
                 | TyAbs(Bvar,Body) => TyAbs(Bvar,subs Body)
                 | _ => ty)
*)
    in
      vsubs fmap (* (if b then vsubs else subs) *)
    end
end;



(*---------------------------------------------------------------------------*
 * Passes over a type, turning all of the type variables into fresh          *
 * UVars, but doing so consistently by using an env, which is an alist       *
 * from variable names to type variable refs.                                *
 *---------------------------------------------------------------------------*)

local fun replace s env =
        case Lib.assoc1 s env
         of NONE =>
              let val r = new_uvar()
              in ((s, r)::env, SOME r)
              end
          | SOME (_, r) => (env, SOME r)
in
(* needs changing *)
fun rename_tv (ty as PT(ty0, locn)) =
  case ty0 of
    Vartype s => replace s
  | TyApp (ty1, ty2) =>
      rename_tv ty1 >-
      (fn ty1' => rename_tv ty2 >-
      (fn ty2' => return (PT(TyApp(ty1', ty2'), locn))))
  | TyUniv (ty1, ty2) =>
      rename_tv ty1 >-
      (fn ty1' => rename_tv ty2 >-
      (fn ty2' => return (PT(TyUniv(ty1', ty2'), locn))))
  | TyAbst (ty1, ty2) =>
      rename_tv ty1 >-
      (fn ty1' => rename_tv ty2 >-
      (fn ty2' => return (PT(TyAbst(ty1', ty2'), locn))))
  | TyKindConstr {Ty, Kind} =>
      rename_tv Ty >-
      (fn Ty' => return (PT(TyKindConstr {Ty=Ty', Kind=Kind}, locn)))
  | TyRankConstr {Ty, Rank} =>
      rename_tv Ty >-
      (fn Ty' => return (PT(TyRankConstr {Ty=Ty', Rank=Rank}, locn)))
  | _ => return ty

fun rename_typevars ty = valOf (#2 (rename_tv ty []))
end

fun fromType t =
  if Type.is_vartype t then let
      val (str, kd, rk) = dest_vartype_opr t
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
    UVar(ref (SOME ty')) => remove_made_links ty'
  | Vartype(s,kd,rk) => PT(Vartype(s, Prekind.remove_made_links kd, rk), locn)
  | Contype {Thy, Tyop, Kind, Rank} =>
      PT(Contype {Kind=Prekind.remove_made_links Kind, Thy=Thy, Tyop=Tyop, Rank=Rank}, locn)
  | TyApp(ty1, ty2) => PT(TyApp (remove_made_links ty1, remove_made_links ty2), locn)
  | TyUniv(tyv, ty) => PT(TyUniv(remove_made_links tyv, remove_made_links ty), locn)
  | TyAbst(tyv, ty) => PT(TyAbst(remove_made_links tyv, remove_made_links ty), locn)
  | TyKindConstr {Ty, Kind} =>
      PT(TyKindConstr {Ty=remove_made_links Ty, Kind=Prekind.remove_made_links Kind}, locn)
  | TyRankConstr {Ty, Rank} =>
      PT(TyRankConstr {Ty=remove_made_links Ty, Rank=Rank}, locn)
  | _ => ty

val tyvariant = Lexis.gen_variant Lexis.tyvar_vary

(* needs changing *)
fun generate_new_name r (kenv, used_so_far) =
  let val result = tyvariant used_so_far "'a"
      val _ = r := SOME (PT(Vartype (result,Prekind.typ,Prerank.Zerorank), locn.Loc_None))
  in
    ((kenv, result::used_so_far), SOME ())
  end

fun kind_replace_null_links kd (kenv,tenv) =
    let val (kenv', result) = Prekind.replace_null_links kd kenv
    in ((kenv',tenv), result)
    end

(* needs changing *)
(* eta-expansion (see "env" after end below) *is* necessary *)
fun replace_null_links (PT(ty,_)) env = let
in
  case ty of
    UVar (r as ref NONE) => generate_new_name r
  | UVar (ref (SOME ty)) => replace_null_links ty
  | TyApp (ty1,ty2) => replace_null_links ty1 >> replace_null_links ty2 >> ok
  | TyUniv (tyv, ty) => replace_null_links tyv >> replace_null_links ty >> ok
  | TyAbst (tyv, ty) => replace_null_links tyv >> replace_null_links ty >> ok
  | TyKindConstr {Ty,Kind} => replace_null_links Ty >> kind_replace_null_links Kind >> ok
  | TyRankConstr {Ty,Rank} => replace_null_links Ty >> ok
  | Vartype (s,kd,rk) => kind_replace_null_links kd
  | Contype {Thy,Tyop,Kind,Rank} => kind_replace_null_links Kind
end env

fun clean (PT(ty, locn)) =
  case ty of
    Vartype (s,kd,rk) => Type.mk_vartype_opr (s, Prekind.toKind kd, Prerank.toRank rk)
  | Contype {Thy,Tyop,...} => Type.mk_thy_con_type {Thy=Thy, Tyop=Tyop}
  | TyApp(ty1,ty2)  => Type.mk_app_type  (clean ty1, clean ty2)
  | TyUniv (tyv,ty) => Type.mk_univ_type (clean tyv, clean ty)
  | TyAbst (tyv,ty) => Type.mk_abs_type  (clean tyv, clean ty)
  | TyKindConstr {Ty,Kind} => clean Ty
  | TyRankConstr {Ty,Rank} => clean Ty
  | _ => raise Fail "Don't expect to see links remaining at this stage of type inference"

fun toType ty =
  let 
      val _ = replace_null_links ty (kindvars ty, tyvars ty)
  in
    clean (remove_made_links ty)
  end

val fun_tyc0 = Contype{Tyop = "fun", Thy = "min",
                       Kind = Prekind.mk_arity 2, Rank = Prerank.Zerorank}

(* chase returns the effective range of an effective function type *)

fun chase (PT(TyApp(PT(TyApp(PT(tyc, _), _), _), ty), _)) =
    if eq0 tyc fun_tyc0 then ty else raise Fail "chase applied to non-function type"
  | chase (PT(UVar(ref (SOME ty)), _)) = chase ty
  | chase _ = raise Fail "chase applied to non-function type"


(*---------------------------------------------------------------------------
 * Kind inference for HOL types. Looks ugly because of error messages, but is
 * actually very simple, given side-effecting unification.
 *---------------------------------------------------------------------------*)

fun is_atom0 (Vartype _) = true
  | is_atom0 (Contype _) = true
  | is_atom0 (TyKindConstr{Ty,...}) = is_atom Ty
  | is_atom0 (TyRankConstr{Ty,...}) = is_atom Ty
  | is_atom0 (UVar (r as ref NONE)) = false
  | is_atom0 (UVar (r as ref (SOME ty))) = is_atom ty
  | is_atom0 ty = false
and is_atom (PT(pty,locn)) = is_atom0 pty



local
  fun default_kdprinter x = "<kind>"
  fun default_typrinter x = "<hol_type>"
  fun default_tmprinter x = "<term>"
  fun Locn (PT(_,locn)) = locn
in
fun KC printers = let
  val (pty, pkd) =
      case printers
       of SOME (y,z) =>
          let val kdprint = Lib.say o z
              val typrint = Lib.say o y
              fun typrint ty =
                  if Type.is_con_type ty
                  then (Lib.say (y ty ^ " : " ^ z (Type.kind_of ty)
                                      ^ " :<= " ^ Int.toString (Type.rank_of ty)))
                  else Lib.say (y ty)
          in
            (typrint, kdprint)
          end
        | NONE => (Lib.say o default_typrinter, Lib.say o default_kdprinter)
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
          in
            Lib.say "\nKind inference failure: unable to infer a kind \
                              \for the application of\n\n";
            pty opr';
            Lib.say ("\n\n"^locn.toString (Locn opr)^"\n\n");

            if (is_atom opr) then ()
            else(Lib.say"which has kind\n\n";
                 pkd(Type.kind_of opr');
                 Lib.say"\n\n");

            Lib.say "to\n\n"; pty arg';
            Lib.say ("\n\n"^locn.toString (Locn arg)^"\n\n");

            if (is_atom opr) then ()
            else(Lib.say"which has kind\n\n";
                 pkd(Type.kind_of arg');
                 Lib.say"\n\n");

            Lib.say ("kind unification failure message: "^message^"\n");
            Feedback.set_trace "kinds" tmp;
            raise ERRloc"kindcheck" (Locn opr (* arbitrary *)) "failed"
          end)
    | check (PT(TyUniv(Bvar, Body), Locn)) = (check Bvar; check Body)
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
              val real_kind = Prekind.toKind Kind
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
          in
            Lib.say "\nKind inference failure: the type\n\n";
            pty real_type;
            Lib.say ("\n\n"^locn.toString (Locn Ty)^"\n\n");
            if (is_atom Ty) then ()
            else(Lib.say"which has kind\n\n";
                 pkd(Type.kind_of real_type);
                 Lib.say"\n\n");
            Lib.say "can not be constrained to be of kind\n\n";
            pkd real_kind;
            Lib.say ("\n\nkind unification failure message: "^message^"\n");
            Feedback.set_trace "kinds" tmp;
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
          in
            Lib.say "\nRank inference failure: the type\n\n";
            pty real_type;
            Lib.say ("\n\n"^locn.toString (Locn Ty)^"\n\n");
            if (is_atom Ty) then ()
            else(Lib.say"which has rank ";
                 Lib.say (Int.toString (Type.rank_of real_type));
                 Lib.say"\n\n");
            Lib.say "can not be constrained to be of rank ";
            Lib.say (Int.toString real_rank);
            Lib.say ("\n\nrank unification failure message: "^message^"\n");
            Feedback.set_trace "kinds" tmp;
            raise ERRloc "rankcheck" locn "failed"
          end)
(*
        let val real_type = toType Ty
            val real_type_rk = Type.rank_of real_type
            val real_rank = Prerank.toRank Rank
        in
          if real_type_rk >= real_rank then ()
          else (
            Lib.say "\nRank inference failure: the type\n\n";
            pty real_type;
            Lib.say ("\n\n"^locn.toString (Locn Ty)^"\n\n");
            if (is_atom Ty) then ()
            else(Lib.say"which has rank ";
                 Lib.say (Int.toString real_type_rk);
                 Lib.say"\n\n");
            Lib.say "can not be constrained to be of rank ";
            Lib.say (Int.toString real_rank);
            Lib.say"\n\n";
            raise ERRloc "rankcheck" locn "failed")
        end)
*)
    | check _ = ()
in check
end end;

fun typecheck_phase1 pfns pty =
    KC pfns pty
(*
    handle phase1_exn(l,s,kd) => let
           in
             case pfns of
               NONE => (Lib.say s; raise ERRloc "kindcheck" l s)
             | SOME (_, typ, knd) =>
               (Lib.say s;
                Lib.say "Wanted it to have kind:  ";
                Lib.say (knd kd);
                Lib.say "\n";
                raise ERRloc "kindcheck" l s)
           end
*)

val checkkind = KC

fun kindcheck pfns pty0 = let
  val _ = KC pfns pty0
in
  toType pty0
end
(*
   handle phase1_exn(l,s,kd) =>
           case pfns of
             NONE => (Lib.say s; raise ERRloc "kindcheck" l s)
           | SOME (_, typ,knd) =>
             (Lib.say s;
              Lib.say "Wanted it to have kind:  ";
              Lib.say (knd kd);
              Lib.say "\n";
              raise ERRloc "kindcheck" l s)
*)

end; (* Pretype *)
