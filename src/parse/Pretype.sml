structure Pretype :> Pretype =
struct

open HolKernel optmonad;
infix >> >-;


val TCERR = mk_HOL_ERR "Pretype";

 datatype pretype0
    = Vartype of Type.tyvar
    | Contype of {Thy : string, Tyop : string, Kind : Type.kind, Rank : int}
    | TyApp of pretype * pretype
    | TyUniv of Type.tyvar * pretype
    | TyAbst of Type.tyvar * pretype
    | UVar of pretype option ref
 and pretype = PT of pretype0 locn.located

fun ((ty1 as PT(_,loc1)) --> (ty2 as PT(_,loc2))) =
    PT(TyApp(PT(TyApp(PT(Contype {Thy = "min", Tyop = "fun", Kind = mk_arity 2,
                                  Rank = 0},
                         locn.Loc_None),
                      ty1),
                locn.Loc_None),
             ty2),
       locn.between loc1 loc2)

fun tyvars (PT (ty, loc)) =
  case ty of
    Vartype s => [s]
  | Contype s => []
  | TyApp (ty1, ty2) => Lib.union (tyvars ty1) (tyvars ty2)
  | TyUniv _ => raise TCERR "tyvars" "TyUniv"
  | TyAbst _ => raise TCERR "tyvars" "TyAbst"
  | UVar (ref NONE) => []
  | UVar (ref (SOME t')) => tyvars t'

fun uvars_of (PT(ty, loc)) =
    case ty of
      UVar r => [r]
    | TyApp (ty1, ty2) => Lib.union (uvars_of ty1) (uvars_of ty2)
    | TyUniv (tyv, ty) => uvars_of ty
    | TyAbst (tyv, ty) => uvars_of ty
    | _ => []

fun new_uvar () = PT (UVar(ref NONE), locn.Loc_None)

infix ref_occurs_in

fun r ref_occurs_in (PT(value, locn)) =
  case value of
    Vartype _ => false
  | Contype _ => false
  | TyApp(ty1, ty2) => r ref_occurs_in ty1 orelse r ref_occurs_in ty2
  | TyUniv(tyv, ty) => r ref_occurs_in ty
  | TyAbst(tyv, ty) => r ref_occurs_in ty
  | UVar (r' as ref NONE) => r = r'
  | UVar (r' as ref (SOME t)) => r = r' orelse r ref_occurs_in t

infix ref_equiv
fun r ref_equiv (PT(value, locn)) =
  case value of
    UVar (r' as ref NONE) => r = r'
  | UVar (r' as ref (SOME t)) => r = r' orelse r ref_equiv t
  | _ => false

  fun has_free_uvar (PT(pty,_)) =
    case pty of
      UVar (ref NONE)        => true
    | UVar (ref (SOME pty')) => has_free_uvar pty'
    | Vartype _              => false
    | Contype _              => false
    | TyApp(ty1, ty2)        => has_free_uvar ty1 orelse has_free_uvar ty2
    | TyAbst(tyv, ty)        => has_free_uvar ty
    | TyUniv(tyv, ty)        => has_free_uvar ty


fun unsafe_bind f r value =
  if r ref_equiv value
  then ok
  else if r ref_occurs_in value orelse isSome (!r)
       then fail
    else (fn acc => (((r, !r)::acc, SOME ()) before r := SOME value))

(* this will need changing *)
(* eta-expansion *is* necessary *)
fun gen_unify bind (ty1 as PT(t1,locn1)) (ty2 as PT(t2,locn2)) e = let
  val gen_unify = gen_unify bind
in
  case (t1, t2) of
    (UVar (r as ref NONE), _) => bind gen_unify r ty2
  | (UVar (r as ref (SOME t1)), t2) => gen_unify t1 ty2
  | (_, UVar _) => gen_unify ty2 ty1
  | (Vartype s1, Vartype s2) => if s1 = s2 then ok else fail
  | (TyApp(ty11, ty12), TyApp(ty21, ty22)) =>
       gen_unify ty11 ty21 >> gen_unify ty12 ty22 >> return ()
  | (Contype r1, Contype r2) => if r1 = r2 then ok else fail
  | _ => fail
 end e

fun unify t1 t2 =
  case (gen_unify unsafe_bind t1 t2 [])
   of (bindings, SOME ()) => ()
    | (_, NONE) => raise TCERR "unify" "unify failed";

fun can_unify t1 t2 = let
  val (bindings, result) = gen_unify unsafe_bind t1 t2 []
  val _ = app (fn (r, oldvalue) => r := oldvalue) bindings
in
  isSome result
end

local
  fun (r ref_equiv (PT(value, locn))) env =
       case value of
         UVar (r' as ref NONE) =>
              r = r' orelse
              let in
                case Lib.assoc1 r' env
                 of NONE => false
                  | SOME (_, v) => (r ref_equiv v) env
              end
         | UVar (ref (SOME t)) => (r ref_equiv t) env
         | _ => false

      fun (r ref_occurs_in (PT(value, locn))) env =
        case value
         of UVar (r' as ref NONE) =>
              r = r' orelse
              let in
                case Lib.assoc1 r' env
                 of NONE => false
                  | SOME (_, v) => (r ref_occurs_in v) env
              end
          | UVar (ref (SOME t)) => (r ref_occurs_in t) env
          | TyApp(ty1,ty2) => (r ref_occurs_in ty1) env orelse
                              (r ref_occurs_in ty2) env
          | TyUniv(tyv, ty) => (r ref_occurs_in ty) env
          | TyAbst(tyv, ty) => (r ref_occurs_in ty) env
          | _ => false
in
fun safe_bind unify r value env =
  case Lib.assoc1 r env
   of SOME (_, v) => unify v value env
    | NONE =>
        if (r ref_equiv value) env then ok env else
        if (r ref_occurs_in value) env then fail env
        else ((r,value)::env, SOME ())
end


fun safe_unify t1 t2 = gen_unify safe_bind t1 t2

(* needs changing *)
fun apply_subst subst (pt as PT (pty, locn)) =
  case pty of
    Vartype _ => pt
  | Contype _ => pt
  | TyApp(ty1, ty2) => PT (TyApp(apply_subst subst ty1, apply_subst subst ty2), locn)
  | TyUniv _ => raise TCERR "apply_subst" "TyUniv"
  | TyAbst _ => raise TCERR "apply_subst" "TyAbst"
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
  | _ => return ty

fun rename_typevars ty = valOf (#2 (rename_tv ty []))
end

fun fromType t =
  if Type.is_vartype t then
    PT(Vartype (dest_vartype_opr t), locn.Loc_None)
  else if Type.is_app_type t then let
      val (ty1, ty2) = Type.dest_app_type t
    in
      PT(TyApp(fromType ty1, fromType ty2), locn.Loc_None)
    end
  else if Type.is_con_type t then
    PT(Contype (dest_thy_con_type t), locn.Loc_None)
  else raise TCERR "fromType" "Unexpected sort of type"

fun remove_made_links (ty as PT(ty0,locn)) =
  case ty0 of
    UVar(ref (SOME ty')) => remove_made_links ty'
  | TyApp(ty1, ty2) => PT(TyApp(remove_made_links ty1, remove_made_links ty2), locn)
  | TyUniv (tyv, ty) => PT(TyUniv(tyv, remove_made_links ty), locn)
  | TyAbst (tyv, ty) => PT(TyAbst(tyv, remove_made_links ty), locn)
  | _ => ty

val tyvariant = Lexis.gen_variant Lexis.tyvar_vary

(* needs changing *)
fun generate_new_name r used_so_far =
  let val result = tyvariant used_so_far "'a"
      val _ = r := SOME (PT(Vartype (result,Kind.typ,0), locn.Loc_None))
  in
    (result::used_so_far, SOME ())
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
  | Vartype _ => ok
  | Contype _ => ok
end env

fun clean (PT(ty, locn)) =
  case ty of
    Vartype s => Type.mk_vartype_opr s
  | Contype r => Type.mk_thy_con_type { Thy = #Thy r, Tyop = #Tyop r}
  | TyApp(ty1,ty2) => Type.mk_app_type (clean ty1, clean ty2)
  | TyUniv (tyv,ty) => Type.mk_univ_type (Type.mk_vartype_opr tyv, clean ty)
  | TyAbst (tyv,ty) => Type.mk_abs_type (Type.mk_vartype_opr tyv, clean ty)
  | _ => raise Fail "Don't expect to see links remaining at this stage"

fun toType ty =
  let val _ = replace_null_links ty (map #1 (tyvars ty))
  in
    clean (remove_made_links ty)
  end

val fun_tyc0 = Contype{Tyop = "fun", Thy = "min", Kind = mk_arity 2, Rank = 0}

fun chase (PT(TyApp(PT(TyApp(PT(tyc, _), _), _), ty), _)) =
    if tyc = fun_tyc0 then ty else raise Fail "chase applied to non-function type"
  | chase (PT(UVar(ref (SOME ty)), _)) = chase ty
  | chase _ = raise Fail "chase applied to non-function type"

end;
