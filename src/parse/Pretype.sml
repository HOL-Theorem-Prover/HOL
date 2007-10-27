structure Pretype :> Pretype =
struct

open HolKernel optmonad;
infix >> >-;

  type prekind = Prekind.prekind
  type kind = Kind.kind
  type hol_type = Type.hol_type
  type pretyvar = string * prekind * int (* rank *)
  type tyvar = Type.tyvar

val TCERR = mk_HOL_ERR "Pretype";

 datatype pretype0
    = Vartype of pretyvar
    | Contype of {Thy : string, Tyop : string, Kind : prekind, Rank : int}
    | TyApp  of pretype * pretype
    | TyUniv of pretype * pretype
    | TyAbst of pretype * pretype
    | TyConstrained of {Ty : pretype, Kind : prekind, Rank : int}
    | UVar of pretype option ref
 and pretype = PT of pretype0 locn.located

(*---------------------------------------------------------------------------
     Location-ignoring equality for pretypes.
 ---------------------------------------------------------------------------*)

val eq_kind = Prekind.eq

fun eq_tyvar (s,kd,rk) (s',kd',rk') = s=s' andalso eq_kind kd kd' andalso rk=rk'

fun eq0 (Vartype v)                (Vartype v')              = eq_tyvar v v'
  | eq0 (Contype{Tyop=Tyop, Thy=Thy, Kind=Kind, Rank=Rank })
        (Contype{Tyop=Tyop',Thy=Thy',Kind=Kind',Rank=Rank'}) = Tyop=Tyop' andalso Thy=Thy' andalso
                                                                 eq_kind Kind Kind' andalso Rank=Rank'
  | eq0 (TyApp(ty1,ty2))           (TyApp(ty1',ty2'))        = eq ty1 ty1' andalso eq ty2 ty2'
  | eq0 (TyUniv(ty1,ty2))          (TyUniv(ty1',ty2'))       = eq ty1 ty1' andalso eq ty2 ty2'
  | eq0 (TyAbst(ty1,ty2))          (TyAbst(ty1',ty2'))       = eq ty1 ty1' andalso eq ty2 ty2'
  | eq0 (TyConstrained{Ty=ty, Kind=kd, Rank=rk })
        (TyConstrained{Ty=ty',Kind=kd',Rank=rk'})            = eq ty ty' andalso eq_kind kd kd' andalso rk=rk'
  | eq0 (UVar (r as ref NONE))     (UVar (r' as ref NONE))   = r=r'
  | eq0 (UVar (ref (SOME ty)))     (UVar (ref (SOME ty')))   = eq ty ty'
  | eq0 _                          _                         = false
and eq  (PT (value,locn))          (PT (value',locn'))       = eq0 value value'

fun ((ty1 as PT(_,loc1)) --> (ty2 as PT(_,loc2))) =
    PT(TyApp(PT(TyApp(PT(Contype {Thy = "min", Tyop = "fun",
                                  Kind = Prekind.mk_arity 2, Rank = 0},
                         locn.Loc_None),
                      ty1),
                locn.Loc_None),
             ty2),
       locn.between loc1 loc2)

fun mk_app_type(ty1 as PT(_,loc1), ty2 as PT(_,loc2)) =
    PT(TyApp(ty1,ty2), locn.between loc1 loc2)

fun dest_app_type(ty as PT(TyApp(ty1,ty2),loc)) = (ty1,ty2)
  | dest_app_type _ = raise TCERR "dest_app_type" "not a type application";

fun mk_univ_type(ty1 as PT(_,loc1), ty2 as PT(_,loc2)) =
    PT(TyUniv(ty1,ty2), locn.between loc1 loc2)

fun dest_univ_type(ty as PT(TyUniv(ty1,ty2),loc)) = (ty1,ty2)
  | dest_univ_type _ = raise TCERR "dest_univ_type" "not a universal type";

fun mk_abs_type(ty1 as PT(_,loc1), ty2 as PT(_,loc2)) =
    PT(TyAbst(ty1,ty2), locn.between loc1 loc2)

fun dest_abs_type(ty as PT(TyAbst(ty1,ty2),loc)) = (ty1,ty2)
  | dest_abs_type _ = raise TCERR "dest_abs_type" "not a type abstraction";

(* returns a list of strings, names of all kind variables mentioned *)
fun kindvars (PT (ty, loc)) =
  case ty of
    Vartype (_, kd, _) => Prekind.kindvars kd
  | Contype{Kind=Kind, ...} => Prekind.kindvars Kind
  | TyApp (ty1, ty2) => Lib.union (kindvars ty1) (kindvars ty2)
  | TyUniv (tyv, ty) => Lib.union (kindvars tyv) (kindvars ty)
  | TyAbst (tyv, ty) => Lib.union (kindvars tyv) (kindvars ty)
  | TyConstrained {Ty,Kind,...} => Lib.union (kindvars Ty) (Prekind.kindvars Kind)
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
  | TyConstrained {Ty,...} => tyvars Ty
  | UVar (ref NONE) => []
  | UVar (ref (SOME ty')) => tyvars ty'

(* returns a list of references, refs of all unification variables mentioned *)
fun uvars_of (PT(ty, loc)) =
    case ty of
      UVar r => [r]
    | TyApp (ty1, ty2) => Lib.union (uvars_of ty1) (uvars_of ty2)
    | TyUniv (tyv, ty) => Lib.union (uvars_of tyv) (uvars_of ty)
    | TyAbst (tyv, ty) => Lib.union (uvars_of tyv) (uvars_of ty)
    | TyConstrained {Ty, ...} => uvars_of Ty
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
  | TyConstrained {Ty, Kind, Rank} => r ref_occurs_in Ty
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
    | TyConstrained {Ty, Kind, Rank} => has_free_uvar_kind Ty orelse Prekind.has_free_uvar Kind

  fun has_free_uvar (PT(pty,_)) =
    case pty of
      UVar (ref NONE)        => true
    | UVar (ref (SOME pty')) => has_free_uvar pty'
    | Vartype _              => false
    | Contype _              => false
    | TyApp(ty1, ty2)        => has_free_uvar ty1 orelse has_free_uvar ty2
    | TyAbst(tyv, ty)        => has_free_uvar tyv orelse has_free_uvar ty
    | TyUniv(tyv, ty)        => has_free_uvar tyv orelse has_free_uvar ty
    | TyConstrained {Ty, Kind, Rank} => has_free_uvar Ty


(*
fun kind_bind f r value (kd_env,ty_env) =
  let val (kd_env', result) = Prekind.safe_bind f r value kd_env
  in ((kd_env',ty_env), result)
  end
*)

fun kind_unify k1 k2 (kd_env,ty_env) =
  let val (kd_env', result) = Prekind.unsafe_unify k1 k2 kd_env
  in ((kd_env',ty_env), result)
  end

fun unsafe_bind f r value =
  if r ref_equiv value
  then ok
  else if r ref_occurs_in value orelse isSome (!r)
       then fail
    else (fn (kd_env,acc) => (((kd_env,(r, !r)::acc), SOME ()) before r := SOME value))


(* first argument is a function which performs a binding between a
   pretype reference and another pretype, updating some sort of environment
   (the 'a), returning the new alpha and a unit option, SOME () for a
   success, and a NONE, if not.

   To further complicate things, the bind argument also gets a copy of
   gen_unify to call, if it should choose.
*)
(* The environment should be a pair:
     a kind environment CROSS the prior type environment.  *)
(* this will need changing *)
(* eta-expansion *is* necessary *)
fun gen_unify (kind_unify:prekind -> prekind -> ('a -> 'a * unit option))
              bind (ty1 as PT(t1,locn1)) (ty2 as PT(t2,locn2)) e = let
  val gen_unify = gen_unify kind_unify bind
in
  case (t1, t2) of
    (UVar (r as ref NONE), _) => bind gen_unify r ty2
  | (UVar (r as ref (SOME t1)), t2) => gen_unify t1 ty2
  | (_, UVar _) => gen_unify ty2 ty1
  | (Vartype (tv1 as (_,k1,_)), Vartype (tv2 as (_,k2,_))) =>
       kind_unify k1 k2 >> (if eq_tyvar tv1 tv2 then ok else fail)
  | (Contype {Kind=k1,...}, Contype {Kind=k2,...}) =>
       kind_unify k1 k2 >> (if eq0 t1 t2 then ok else fail)
  | (TyApp(ty11, ty12), TyApp(ty21, ty22)) =>
       gen_unify ty11 ty21 >> gen_unify ty12 ty22 >> return ()
  | (TyUniv(ty11, ty12), TyUniv(ty21, ty22)) =>
       gen_unify ty11 ty21 >> gen_unify ty12 ty22 >> return ()
  | (TyAbst(ty11, ty12), TyAbst(ty21, ty22)) =>
       gen_unify ty11 ty21 >> gen_unify ty12 ty22 >> return ()
  | (TyConstrained{Ty=ty1,Kind=kd1,Rank=rk1}, TyConstrained{Ty=ty2,Kind=kd2,Rank=rk2}) =>
       if rk1=rk2 then kind_unify kd1 kd2 >> gen_unify ty1 ty2 >> return () else fail
  | _ => fail
 end e

val empty_env = ([]:(prekind option ref * prekind option) list,
                 []:(pretype option ref * pretype option) list)

fun unify t1 t2 =
  case (gen_unify kind_unify unsafe_bind t1 t2 empty_env)
   of (bindings, SOME ()) => ()
    | (_, NONE) => raise TCERR "unify" "unify failed";

fun can_unify t1 t2 = let
  val ((kind_bindings,type_bindings), result) =
        gen_unify kind_unify unsafe_bind t1 t2 empty_env
  val _ = app (fn (r, oldvalue) => r := oldvalue) kind_bindings
  val _ = app (fn (r, oldvalue) => r := oldvalue) type_bindings
in
  isSome result
end

local
  fun (r ref_equiv (PT(value, locn))) (env as (kenv,tenv)) =
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

      fun (r ref_occurs_in (PT(value, locn))) (env as (kenv,tenv)) =
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
          | TyConstrained{Ty,...} => (r ref_occurs_in Ty) env
          | _ => false

      fun kind_unify k1 k2 (env as (kenv,tenv)) =
        let val (kenv', result) = Prekind.safe_unify k1 k2 kenv
        in ((kenv',tenv), result)
        end

in
fun safe_bind unify r value (env as (kenv,tenv)) =
  case Lib.assoc1 r tenv
   of SOME (_, v) => unify v value env
    | NONE =>
        if (r ref_equiv value) env then ok env else
        if (r ref_occurs_in value) env then fail env
        else ((kenv,(r,value)::tenv), SOME ())

fun safe_unify t1 t2 = gen_unify kind_unify safe_bind t1 t2
end


fun apply_subst subst (pt as PT (pty, locn)) =
  case pty of
    Vartype _ => pt
  | Contype _ => pt
  | TyApp(ty1, ty2) => PT (TyApp(apply_subst subst ty1, apply_subst subst ty2), locn)
  | TyUniv(bty, body) => PT (TyUniv(apply_subst subst bty, apply_subst subst body), locn)
  | TyAbst(bty, body) => PT (TyAbst(apply_subst subst bty, apply_subst subst body), locn)
  | TyConstrained {Ty, Kind, Rank} =>
                 PT (TyConstrained {Ty=apply_subst subst Ty, Kind=Kind, Rank=Rank}, locn)
  | UVar (ref (SOME t)) => apply_subst subst t
  | UVar (r as ref NONE) =>
      case (Lib.assoc1 r subst) of
        NONE => pt
      | SOME (_, value) => apply_subst subst value

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
  | TyConstrained {Ty, Kind, Rank} =>
      rename_tv Ty >-
      (fn Ty' => return (PT(TyConstrained {Ty=Ty', Kind=Kind, Rank=Rank}, locn)))
  | _ => return ty

fun rename_typevars ty = valOf (#2 (rename_tv ty []))
end

fun fromType t =
  if Type.is_vartype t then let
      val (str, kd, rk) = dest_vartype_opr t
    in
      PT(Vartype (str, Prekind.fromKind kd, rk), locn.Loc_None)
    end
  else if Type.is_con_type t then let
      val {Thy, Tyop, Kind, Rank} = dest_thy_con_type t
    in
      PT(Contype {Kind=Prekind.fromKind Kind,
                  Thy=Thy, Tyop=Tyop, Rank=Rank}, locn.Loc_None)
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
  | TyConstrained {Ty, Kind, Rank} =>
      PT(TyConstrained {Ty=remove_made_links Ty, Kind=Prekind.remove_made_links Kind, Rank=Rank}, locn)
  | _ => ty

val tyvariant = Lexis.gen_variant Lexis.tyvar_vary

(* needs changing *)
fun generate_new_name r (kenv, used_so_far) =
  let val result = tyvariant used_so_far "'a"
      val _ = r := SOME (PT(Vartype (result,Prekind.typ,0), locn.Loc_None))
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
  | TyUniv (tyv, ty) => replace_null_links ty
  | TyAbst (tyv, ty) => replace_null_links ty
  | TyConstrained {Ty,Kind,Rank} => replace_null_links Ty >> kind_replace_null_links Kind >> ok
  | Vartype (s,kd,rk) => kind_replace_null_links kd
  | Contype {Thy,Tyop,Kind,Rank} => kind_replace_null_links Kind
end env

fun clean (PT(ty, locn)) =
  case ty of
    Vartype (s,kd,rk) => Type.mk_vartype_opr (s, Prekind.clean kd, rk)
  | Contype {Thy,Tyop,...} => Type.mk_thy_con_type {Thy=Thy, Tyop=Tyop}
  | TyApp(ty1,ty2) => Type.mk_app_type (clean ty1, clean ty2)
  | TyUniv (tyv,ty) => Type.mk_univ_type (clean tyv, clean ty)
  | TyAbst (tyv,ty) => Type.mk_abs_type (clean tyv, clean ty)
  | TyConstrained {Ty,Kind,Rank} => clean Ty
  | _ => raise Fail "Don't expect to see links remaining at this stage"

fun toType ty =
  let 
      val _ = replace_null_links ty (kindvars ty, tyvars ty)
  in
    clean (remove_made_links ty)
  end

val fun_tyc0 = Contype{Tyop = "fun", Thy = "min", Kind = Prekind.mk_arity 2, Rank = 0}

(* chase returns the effective range of an effective function type *)

fun chase (PT(TyApp(PT(TyApp(PT(tyc, _), _), _), ty), _)) =
    if eq0 tyc fun_tyc0 then ty else raise Fail "chase applied to non-function type"
  | chase (PT(UVar(ref (SOME ty)), _)) = chase ty
  | chase _ = raise Fail "chase applied to non-function type"

end;
