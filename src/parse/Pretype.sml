structure Pretype :> Pretype =
struct

open HolKernel optmonad;
infix >> >-;
infixr ==>;

  type prerank = Prerank.prerank
  type oprerank = Prerank.oprerank
  type prekind = Prekind.prekind
  type uvarkind = Prekind.uvarkind
  type kind = Kind.kind
  type hol_type = Type.hol_type
  type pretyvar = string * prekind
  type tyvar = Type.tyvar

fun is_debug() = current_trace "debug_type_inference" >= 3;
fun ho_debug() = current_trace "debug_type_inference" >= 1;

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
       | TyExisFail of hol_type
       | TyKindConstrFail of hol_type * kind
       | TyRankConstrFail of hol_type * rank
       | TyRankLEConstrFail of hol_type * rank
    (* | TyHOmatchFail *)

val last_kcerror : (kcheck_error * locn.locn) option ref = ref NONE

 datatype pretype0
    = Vartype of pretyvar
    | Contype of {Thy : string, Tyop : string, Kind : prekind}
    | TyApp  of pretype * pretype
    | TyUniv of pretype * pretype
    | TyExis of pretype * pretype
    | TyAbst of pretype * pretype
    | TyKindConstr of {Ty : pretype, Kind : prekind}
    | TyRankConstr of {Ty : pretype, Rank : prerank}
    | UVar of uvartype ref
 and uvartype
    = SOMEU of pretype
    | NONEU of prekind
 and pretype = PT of pretype0 locn.located

fun isSomeU (SOMEU _) = true
  | isSomeU (NONEU _) = false

fun THEU (SOMEU v) = v
  | THEU (NONEU _) = raise TCERR "THEU" "uvartype not a SOMEU";

fun tylocn (PT(_,locn)) = locn

fun bool_str true = "true" | bool_str false = "false"

(*---------------------------------------------------------------------------
  Location-ignoring but alpha-equivalence respecting equality for pretypes.
 ---------------------------------------------------------------------------*)

val eq_rank = Prerank.eq
val le_rank = Prerank.leq
val eq_kind = Prekind.eqr (* disregards ranks *)
val ge_kind = Prekind.ge

fun eq_tyvar (s,kd) (s',kd') = s=s' (*andalso eq_kind kd kd'*)
(* kind comparison omitted because in parser, kinds might not be fully unified yet *)
fun eq_tyvar_kinds (s,kd) (s',kd') = eq_kind kd kd'

fun Vartype_of0 (Vartype v) = v
  | Vartype_of0 (TyKindConstr{Ty, Kind}) =
       let val (s,kd) = Vartype_of Ty in (s,Kind) end
  | Vartype_of0 (TyRankConstr{Ty, Rank}) =
       let val (s,kd) = Vartype_of Ty in (s,kd) end
  | Vartype_of0 _ = raise TCERR "Vartype_of" "not a variable or a kind or rank constraint"
and Vartype_of (PT(ty,locn)) = Vartype_of0 ty;

fun eq_varty   []      []    v v' = eq_tyvar v v'
  | eq_varty (x::xs) (y::ys) v v' =
      let val x_eq_v  = eq_tyvar x v
          and y_eq_v' = eq_tyvar y v'
      in (x_eq_v andalso y_eq_v') orelse
         (not x_eq_v andalso not y_eq_v' andalso eq_varty xs ys v v')
      end
  | eq_varty   _       _     _ _  = false

val ge_varty = eq_varty (* for now, since kind comparison omitted *)

fun eq_env0 e1 e2 (Vartype v)                (Vartype v')              = eq_varty e1 e2 v v'
  | eq_env0 e1 e2 (Contype{Tyop=Tyop, Thy=Thy, Kind=Kind })
                  (Contype{Tyop=Tyop',Thy=Thy',Kind=Kind'})            = Tyop=Tyop' andalso Thy=Thy'
                                                                           andalso eq_kind Kind Kind'
  | eq_env0 e1 e2 (TyApp(ty1,ty2))           (TyApp(ty1',ty2'))        = eq_env e1 e2 ty1 ty1' andalso eq_env e1 e2 ty2 ty2'
  | eq_env0 e1 e2 (TyUniv(ty1,ty2))          (TyUniv(ty1',ty2'))       =
          eq_tyvar_kinds (Vartype_of ty1) (Vartype_of ty1') andalso
          eq_env (Vartype_of ty1::e1) (Vartype_of ty1'::e2) ty2 ty2'
  | eq_env0 e1 e2 (TyExis(ty1,ty2))          (TyExis(ty1',ty2'))       =
          eq_tyvar_kinds (Vartype_of ty1) (Vartype_of ty1') andalso
          eq_env (Vartype_of ty1::e1) (Vartype_of ty1'::e2) ty2 ty2'
  | eq_env0 e1 e2 (TyAbst(ty1,ty2))          (TyAbst(ty1',ty2'))       =
          eq_tyvar_kinds (Vartype_of ty1) (Vartype_of ty1') andalso
          eq_env (Vartype_of ty1::e1) (Vartype_of ty1'::e2) ty2 ty2'
  | eq_env0 e1 e2 (TyKindConstr{Ty=ty, Kind=kd })
                  (TyKindConstr{Ty=ty',Kind=kd'})                      = eq_env e1 e2 ty ty' andalso eq_kind kd kd'
  | eq_env0 e1 e2 (TyRankConstr{Ty=ty, Rank=rk })
                  (TyRankConstr{Ty=ty',Rank=rk'})                      = eq_env e1 e2 ty ty' andalso eq_rank rk rk'
  | eq_env0 e1 e2 (UVar (r  as ref (NONEU _)))
                  (UVar (r' as ref (NONEU _)))                         = r=r'
  | eq_env0 e1 e2 (UVar (ref (SOMEU ty)))    (UVar (ref (SOMEU ty')))  = eq_env e1 e2 ty ty'
  | eq_env0 e1 e2 (UVar (ref (SOMEU ty)))    ty'                       = eq_env e1 e2 ty (PT(ty',locn.Loc_None))
  | eq_env0 e1 e2 ty                         (UVar (ref (SOMEU ty')))  = eq_env e1 e2 (PT(ty,locn.Loc_None)) ty'
  | eq_env0 e1 e2 _                          _                         = false
and eq_env  e1 e2 (PT (value,locn))          (PT (value',locn'))       = eq_env0 e1 e2 value value'

val eq0 = eq_env0 [] []
and eq  = eq_env  [] [];

fun ge_env0 e1 e2 (Vartype v)                (Vartype v')              = ge_varty e1 e2 v v'
  | ge_env0 e1 e2 (Contype{Tyop=Tyop, Thy=Thy, Kind=Kind })
                  (Contype{Tyop=Tyop',Thy=Thy',Kind=Kind'})            = Tyop=Tyop' andalso Thy=Thy'
                                                                           andalso ge_kind Kind Kind'
  | ge_env0 e1 e2 (TyApp(ty1,ty2))           (TyApp(ty1',ty2'))        = ge_env e1 e2 ty1 ty1' andalso ge_env e1 e2 ty2 ty2'
  | ge_env0 e1 e2 (TyUniv(ty1,ty2))          (TyUniv(ty1',ty2'))       =
          eq_tyvar_kinds (Vartype_of ty1) (Vartype_of ty1') andalso
          ge_env (Vartype_of ty1::e1) (Vartype_of ty1'::e2) ty2 ty2'
  | ge_env0 e1 e2 (TyExis(ty1,ty2))          (TyExis(ty1',ty2'))       =
          eq_tyvar_kinds (Vartype_of ty1) (Vartype_of ty1') andalso
          ge_env (Vartype_of ty1::e1) (Vartype_of ty1'::e2) ty2 ty2'
  | ge_env0 e1 e2 (TyAbst(ty1,ty2))          (TyAbst(ty1',ty2'))       =
          eq_tyvar_kinds (Vartype_of ty1) (Vartype_of ty1') andalso
          ge_env (Vartype_of ty1::e1) (Vartype_of ty1'::e2) ty2 ty2'
  | ge_env0 e1 e2 (TyKindConstr{Ty=ty, Kind=kd })
                  (TyKindConstr{Ty=ty',Kind=kd'})                      = ge_env e1 e2 ty ty' andalso ge_kind kd kd'
  | ge_env0 e1 e2 (TyRankConstr{Ty=ty, Rank=rk })
                  (TyRankConstr{Ty=ty',Rank=rk'})                      = ge_env e1 e2 ty ty' andalso le_rank rk' rk
  | ge_env0 e1 e2 (UVar (r  as ref (NONEU _)))
                  (UVar (r' as ref (NONEU _)))                         = r=r'
  | ge_env0 e1 e2 (UVar (ref (SOMEU ty)))    (UVar (ref (SOMEU ty')))  = ge_env e1 e2 ty ty'
  | ge_env0 e1 e2 (UVar (ref (SOMEU ty)))    ty'                       = ge_env e1 e2 ty (PT(ty',locn.Loc_None))
  | ge_env0 e1 e2 ty                         (UVar (ref (SOMEU ty')))  = ge_env e1 e2 (PT(ty,locn.Loc_None)) ty'
  | ge_env0 e1 e2 _                          _                         = false
and ge_env  e1 e2 (PT (value,locn))          (PT (value',locn'))       = ge_env0 e1 e2 value value'

val ge0 = ge_env0 [] []
and ge  = ge_env  [] [];

fun list_eq (e1::es1) (e2::es2) = eq e1 e2 andalso list_eq es1 es2
  | list_eq [] [] = true
  | list_eq _ _ = false;

(*val prekind_rank_compare = Lib.pair_compare(Prekind.prekind_compare, Prerank.prerank_compare);*)

val prekind_compare = Prekind.prekind_compare

fun pretyvar_compare ((s1,kd1), (s2,kd2)) =
       (case String.compare (s1,s2)
         of EQUAL => prekind_compare (kd1,kd2)
          | x => x)

fun pretype_var_compare (Vartype u, Vartype v) = pretyvar_compare (u,v)
  | pretype_var_compare _ = raise TCERR "pretype_var_compare" "variables required";

fun pretype_con_compare (Contype{Tyop=Tyop1, Thy=Thy1, Kind=Kind1},
                         Contype{Tyop=Tyop2, Thy=Thy2, Kind=Kind2}) =
       (case Lib.pair_compare(String.compare,String.compare)((Thy1,Tyop1),(Thy2,Tyop2))
         of EQUAL => prekind_compare (Kind1,Kind2)
          | x => x)
  | pretype_con_compare _ =raise TCERR "pretype_con_compare" "constants required";

(* ----------------------------------------------------------------------
    A total ordering on pretypes that does not respect alpha equivalence.
       It does ignore locations.
    Vartype < Contype < TyApp < TyUniv < TyExis < TyAbst < TyKindConstr < TyRankConstr
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
    | (TyExis _, Vartype _)              => GREATER
    | (TyExis _, Contype _)              => GREATER
    | (TyExis _, TyApp _)                => GREATER
    | (TyExis _, TyUniv _)               => GREATER
    | (TyExis(bv1,ty1), TyExis(bv2,ty2)) =>
                            Lib.pair_compare(compare,compare) ((bv1,ty1),(bv2,ty2))
    | (TyExis _, _)                      => LESS
    | (TyAbst _, Vartype _)              => GREATER
    | (TyAbst _, Contype _)              => GREATER
    | (TyAbst _, TyApp _)                => GREATER
    | (TyAbst _, TyUniv _)               => GREATER
    | (TyAbst _, TyExis _)               => GREATER
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
    | (UVar (ref(NONEU kd1)), UVar (ref(NONEU kd2))) => prekind_compare (kd1,kd2)
    | (UVar (ref(NONEU _)), _)           => GREATER
    | (UVar (ref(SOMEU ty1)), UVar (ref(SOMEU ty2))) => compare(ty1,ty2)
    | (UVar (ref(SOMEU _)), _)           => GREATER
;

fun is_var_type(PT(Vartype v,loc)) = true
  | is_var_type _ = false

fun is_uvar_type(PT(UVar r,loc)) = true
  | is_uvar_type _ = false

fun is_uvar_NONE_type(PT(UVar(ref(NONEU _)),_)) = true
  | is_uvar_NONE_type _ = false

fun has_var_type(ty as PT(Vartype v,loc)) = true
  | has_var_type(PT(TyKindConstr{Ty,Kind},loc)) = has_var_type Ty
  | has_var_type(PT(TyRankConstr{Ty,Rank},loc)) = has_var_type Ty
  | has_var_type(PT(UVar(ref(SOMEU ty)),loc))   = has_var_type ty
  | has_var_type(ty as PT(UVar(ref(NONEU _)),loc)) = true
  | has_var_type _ = false;

fun has_real_var_type(ty as PT(Vartype v,loc)) = true
  | has_real_var_type(PT(TyKindConstr{Ty,Kind},loc)) = has_real_var_type Ty
  | has_real_var_type(PT(TyRankConstr{Ty,Rank},loc)) = has_real_var_type Ty
  | has_real_var_type(PT(UVar(ref(SOMEU ty)),loc))   = has_real_var_type ty
  | has_real_var_type(ty as PT(UVar(ref(NONEU _)),loc)) = false
  | has_real_var_type _ = false;

fun contains_uvar_type (PT(UVar(ref(NONEU _)),_)) = true
  | contains_uvar_type (PT(UVar(ref(SOMEU ty)),_)) = contains_uvar_type ty
  | contains_uvar_type (PT(TyApp(ty1,ty2),_))  = contains_uvar_type ty1 orelse contains_uvar_type ty2
  | contains_uvar_type (PT(TyExis(ty1,ty2),_)) = contains_uvar_type ty1 orelse contains_uvar_type ty2
  | contains_uvar_type (PT(TyUniv(ty1,ty2),_)) = contains_uvar_type ty1 orelse contains_uvar_type ty2
  | contains_uvar_type (PT(TyAbst(ty1,ty2),_)) = contains_uvar_type ty1 orelse contains_uvar_type ty2
  | contains_uvar_type (PT(TyKindConstr{Ty,Kind},_)) = contains_uvar_type Ty
  | contains_uvar_type (PT(TyRankConstr{Ty,Rank},_)) = contains_uvar_type Ty
  | contains_uvar_type _ = false

val contains_uvar_typel = exists contains_uvar_type

fun dest_var_type(PT(Vartype v,loc)) = v
  | dest_var_type(PT(UVar(ref(SOMEU ty)),loc)) = dest_var_type ty
  | dest_var_type _ = raise TCERR "dest_var_type" "not a type variable";

fun distinct cmp (x::xs) = not (op_mem cmp x xs) andalso distinct cmp xs
  | distinct cmp _ = true

val distinct_vars = distinct eq

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

fun is_con_type ty = can dest_con_type ty;

fun mk_con_type (a,locn) = PT(Contype a, locn)

fun mk_app_type(ty1 as PT(_,loc1), ty2 as PT(_,loc2)) =
    PT(TyApp(ty1,ty2), locn.between loc1 loc2)

fun list_mk_app_type(tyop, ty::tys) = list_mk_app_type(mk_app_type(tyop, ty), tys)
  | list_mk_app_type(tyop,   []   ) = tyop

fun dest_app_type(PT(UVar(ref(SOMEU ty))  ,loc)) = dest_app_type ty
  | dest_app_type(PT(TyKindConstr{Ty,Kind},loc)) = dest_app_type Ty
  | dest_app_type(PT(TyRankConstr{Ty,Rank},loc)) = dest_app_type Ty
  | dest_app_type(PT(TyApp type_pair      ,loc)) = type_pair
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

(*  is_universal is true iff the argument contains a universal or existential type. *)
fun is_universal(PT(UVar(ref(SOMEU ty)),loc)) = is_universal ty
  | is_universal(PT(UVar(ref(NONEU _ )),loc)) = false
  | is_universal(PT(TyKindConstr{Ty,Kind},loc)) = is_universal Ty
  | is_universal(PT(TyRankConstr{Ty,Rank},loc)) = is_universal Ty
  | is_universal(PT(TyUniv(ty1,ty2),loc)) = true
  | is_universal(PT(TyExis(ty1,ty2),loc)) = true
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
      val {Thy, Tyop, Kind} = dest_con_type ty0
  in if Thy = "min" andalso Tyop = "fun"
     then (ty1,ty2)
     else raise ERR "" ""
  end
  handle HOL_ERR _ => raise TCERR "dom_rng" "not a function type";

val is_fun_type = can dom_rng

(* returns a list of strings, names of all kind variables mentioned *)
fun kindvars (PT (ty, loc)) =
  case ty of
    Vartype (_, kd) => Prekind.kindvars kd
  | Contype{Kind=Kind, ...} => Prekind.kindvars Kind
  | TyApp (ty1, ty2) => Lib.union (kindvars ty1) (kindvars ty2)
  | TyUniv (tyv, ty) => Lib.union (kindvars tyv) (kindvars ty)
  | TyExis (tyv, ty) => Lib.union (kindvars tyv) (kindvars ty)
  | TyAbst (tyv, ty) => Lib.union (kindvars tyv) (kindvars ty)
  | TyKindConstr {Ty,Kind} => Lib.union (kindvars Ty) (Prekind.kindvars Kind)
  | TyRankConstr {Ty,... } => kindvars Ty
  | UVar (ref (NONEU kd)) => Prekind.kindvars kd
  | UVar (ref (SOMEU ty')) => kindvars ty'

(* returns a list of strings, names of all type variables mentioned *)
fun tyvars (PT (ty, loc)) =
  case ty of
    Vartype (s, _) => [s]
  | Contype _ => []
  | TyApp (ty1, ty2) => Lib.union (tyvars ty1) (tyvars ty2)
  | TyUniv (tyv, ty) => Lib.union (tyvars tyv) (tyvars ty)
  | TyExis (tyv, ty) => Lib.union (tyvars tyv) (tyvars ty)
  | TyAbst (tyv, ty) => Lib.union (tyvars tyv) (tyvars ty)
  | TyKindConstr {Ty,...} => tyvars Ty
  | TyRankConstr {Ty,...} => tyvars Ty
  | UVar (ref (NONEU _)) => []
  | UVar (ref (SOMEU ty')) => tyvars ty'

(* returns a list of references, refs of all type unification variables mentioned *)
fun uvars_of (PT(ty, loc)) =
    case ty of
      UVar r => [r]
    | TyApp (ty1, ty2) => Lib.union (uvars_of ty1) (uvars_of ty2)
    | TyUniv (tyv, ty) => Lib.union (uvars_of tyv) (uvars_of ty)
    | TyExis (tyv, ty) => Lib.union (uvars_of tyv) (uvars_of ty)
    | TyAbst (tyv, ty) => Lib.union (uvars_of tyv) (uvars_of ty)
    | TyKindConstr {Ty, ...} => uvars_of Ty
    | TyRankConstr {Ty, ...} => uvars_of Ty
    | _ => []

(* returns a list of references, refs of all type unification variables mentioned *)
fun uvars_NONE_of (PT(ty, loc)) =
    case ty of
      UVar (r as ref (NONEU _)) => [r]
    | UVar (ref (SOMEU ty')) => uvars_NONE_of ty'
    | TyApp (ty1, ty2) => Lib.union (uvars_NONE_of ty1) (uvars_NONE_of ty2)
    | TyUniv (tyv, ty) => Lib.union (uvars_NONE_of tyv) (uvars_NONE_of ty)
    | TyExis (tyv, ty) => Lib.union (uvars_NONE_of tyv) (uvars_NONE_of ty)
    | TyAbst (tyv, ty) => Lib.union (uvars_NONE_of tyv) (uvars_NONE_of ty)
    | TyKindConstr {Ty, ...} => uvars_NONE_of Ty
    | TyRankConstr {Ty, ...} => uvars_NONE_of Ty
    | _ => []

fun uvars_NONE_ofl (ty::tys) = Lib.union (uvars_NONE_of ty) (uvars_NONE_ofl tys)
  | uvars_NONE_ofl    []     = []

fun new_uvar kd = PT (UVar(ref (NONEU kd)), locn.Loc_None)

fun all_new_uvar () = new_uvar (Prekind.all_new_uvar())
(*fun new_var_uvar () = new_uvar (Prekind.new_var_uvar())*)

local
val reset_rk = Prerank.reset_rank_uvars
val reset_kd = Prekind.reset_rank_uvars
in
fun reset_rank_uvars0 (UVar (ref(NONEU kd))) = reset_kd kd
  | reset_rank_uvars0 (UVar (ref(SOMEU ty))) = reset_rank_uvars ty
  | reset_rank_uvars0 (Vartype(s,kd)) = reset_kd kd
  | reset_rank_uvars0 (Contype{Thy,Tyop,Kind}) =  reset_kd Kind
  | reset_rank_uvars0 (TyApp(ty1,ty2)) = (reset_rank_uvars ty1; reset_rank_uvars ty2)
  | reset_rank_uvars0 (TyUniv(ty1,ty2)) = (reset_rank_uvars ty1; reset_rank_uvars ty2)
  | reset_rank_uvars0 (TyExis(ty1,ty2)) = (reset_rank_uvars ty1; reset_rank_uvars ty2)
  | reset_rank_uvars0 (TyAbst(ty1,ty2)) = (reset_rank_uvars ty1; reset_rank_uvars ty2)
  | reset_rank_uvars0 (TyKindConstr{Ty,Kind}) = (reset_kd Kind; reset_rank_uvars Ty)
  | reset_rank_uvars0 (TyRankConstr{Ty,Rank}) = (reset_rk Rank; reset_rank_uvars Ty)
and reset_rank_uvars (PT(ty0,_)) = reset_rank_uvars0 ty0
end


(*---------------------------------------------------------------------------*
 * The free type variables in a pretype.  Tail recursive (from Ken Larsen).  *
 *---------------------------------------------------------------------------*)

local val insert = Lib.op_insert eq
      val union  = Lib.op_union eq
      val mem    = Lib.op_mem eq
      val the_var = the_var_type
      fun TV (v as PT(Vartype _,_)) B A k = if mem v B then k A
                                            else k (insert v A)
        | TV (PT(Contype _,_)) B A k      = k A
        | TV (PT(TyApp(opr, arg),_)) B A k= TV opr B A (fn q => TV arg B q k)
        | TV (PT(TyUniv(v,ty),_)) B A k   = TV ty (insert (the_var v) B) A k
        | TV (PT(TyExis(v,ty),_)) B A k   = TV ty (insert (the_var v) B) A k
        | TV (PT(TyAbst(v,ty),_)) B A k   = TV ty (insert (the_var v) B) A k
        | TV (PT(TyKindConstr{Ty,Kind},_)) B A k = TV Ty B A k
        | TV (PT(TyRankConstr{Ty,Rank},_)) B A k = TV Ty B A k
        | TV (PT(UVar(ref(SOMEU ty)),_)) B A k = TV ty B A k
        | TV (v as PT(UVar(ref(NONEU _ )),_)) B A k = if mem v B then k A
                                                      else k (insert v A)
      and TVl (ty::tys) B A k = TV ty B A (fn q => TVl tys B q k)
        | TVl _ B A k = k A
in
fun type_vars ty = rev(TV ty [] [] Lib.I)
fun type_varsl L = rev(TVl L [] [] Lib.I)
fun type_uvars ty = filter is_uvar_type (type_vars ty)
fun type_uvarsl L = filter is_uvar_type (type_varsl L)
end;

fun type_vars_subst (theta : (pretype,pretype)Lib.subst) = type_varsl (map #residue theta);


(*---------------------------------------------------------------------------*
 *    Converting pretypes to strings, for printing.                          *
 *---------------------------------------------------------------------------*)

local open Prekind Prerank Portable
in
fun default_kind (PK(Typekind Zerorank,_)) = true
  | default_kind _ = false
fun pp_if_prekind add_string pp_prekind kd =
      if default_kind kd then ()
      else (add_string ": ";
            pp_prekind kd)
fun kind_to_string (PK(Typekind Zerorank,_)) = ""
  | kind_to_string kd = " :" ^ prekind_to_string kd
fun default_rank Zerorank = true
  | default_rank _ = false
fun add_rank_string Zerorank = ""
  | add_rank_string rk = ":" ^ prerank_to_string rk
fun pp_if_prerank add_string pp_prerank rk =
      if current_trace "ranks" + (if default_rank rk then 0 else 1) < 3 then ()
      else (add_string ":";
            pp_prerank rk)
fun pp_if_prekind_rank add_string pp_prekind pp_prerank kd =
  let val pr_kd = current_trace "kinds" + (if default_kind kd then 0 else 1) > 1
      val rk = Prekind.prank_of kd handle Fail _ => Prerank.new_uvar()
      val pr_rk = if pr_kd then false
                  else current_trace "ranks" + (if default_rank rk then 0 else 1) > 2
  in
      if not pr_kd then ()
      else (add_string ": ";
            pp_prekind kd);
      if not pr_rk then ()
      else (add_string ":<=";
            pp_prerank rk)
  end
end

datatype pp_pty_state = none | left | right | uvar

fun pp_pretype pps ty =
 let open Portable
     val {add_string,add_break,begin_block,end_block,...} = with_ppstream pps
     val checkref = Portable.ref_to_int
     val pp_prekind = Prekind.pp_prekind pps
     val pp_prerank = Prerank.pp_prerank pps
     val pp_if_prekind = pp_if_prekind add_string pp_prekind
     val pp_if_prerank = pp_if_prerank add_string pp_prerank
     val pp_if_prekind_rank = pp_if_prekind_rank add_string pp_prekind pp_prerank
     fun pppretype state (ty as PT(ty0,locn)) =
       case ty0 of
           UVar(r as ref (SOMEU pty')) => let
           in
             if state <> uvar then begin_block INCONSISTENT 0 else ();
             add_string (Int.toString (checkref r) ^ "=");
             add_break (1,2);
             pppretype uvar pty';
             if state <> uvar then end_block() else ()
           end
         | UVar(r as ref (NONEU kd)) => (add_string (Int.toString (checkref r));
                                         pp_if_prekind_rank kd )
         | Vartype(s,kd) => (add_string ("V(" ^ s);
                             pp_if_prekind_rank kd;
                             add_string ")")
         | Contype {Thy, Tyop, Kind} => (if current_trace "ranks" < 3 then () else
                                           add_string "[";
                                         if Thy = "bool" orelse Thy = "min" then
                                           add_string Tyop
                                         else add_string (Thy ^ "$" ^ Tyop);
                                         pp_if_prerank (Prekind.prank_of Kind);
                                         if current_trace "ranks" < 3 then () else
                                           add_string "]" )
         | TyApp(PT(TyApp(PT(Contype{Tyop="fun",Kind,...},_), ty1),_), ty2) =>
                              (if state = none then begin_block INCONSISTENT 0
                               else if state = left orelse state = uvar then
                                   (add_string "("; begin_block INCONSISTENT 0)
                               else ();
                               pppretype left ty1;
                               add_string " ";
                               if current_trace "ranks" < 3 then () else
                                 add_string "[";
                               add_string "->";
                               pp_if_prerank (Prekind.prank_of Kind);
                               if current_trace "ranks" < 3 then () else
                                 add_string "]";
                               add_break(1,0);
                               pppretype right ty2;
                               if state = none then end_block()
                               else if state = left orelse state = uvar then
                                  (end_block(); add_string ")")
                               else ())
         | TyApp(PT(UVar(ref(SOMEU(PT(TyApp(PT(Contype{Tyop="fun",Kind,...},_), ty1),_)))),_), ty2) =>
                              (if state = none then begin_block INCONSISTENT 0
                               else if state = left orelse state = uvar then
                                   (add_string "("; begin_block INCONSISTENT 0)
                               else ();
                               pppretype left ty1;
                               add_string " ";
                               if current_trace "ranks" < 3 then () else
                                 add_string "[";
                               add_string "->";
                               pp_if_prerank (Prekind.prank_of Kind);
                               if current_trace "ranks" < 3 then () else
                                 add_string "]";
                               add_break(1,0);
                               pppretype right ty2;
                               if state = none then end_block()
                               else if state = left orelse state = uvar then
                                  (end_block(); add_string ")")
                               else ())
         | TyApp(PT(TyApp(PT(Contype{Tyop="prod",Kind,...},_), ty1),_), ty2) =>
                              (if state = none then begin_block INCONSISTENT 0
                               else if state = left orelse state = uvar then
                                   (add_string "("; begin_block INCONSISTENT 0)
                               else ();
                               pppretype left ty1;
                               add_string " #";
                               pp_if_prerank (Prekind.prank_of Kind);
                               add_break(1,0);
                               pppretype right ty2;
                               if state = none then end_block()
                               else if state = left orelse state = uvar then
                                  (end_block(); add_string ")")
                               else ())
         | TyApp(PT(TyApp(PT(Contype{Tyop="sum",Kind,...},_), ty1),_), ty2) =>
                              (if state = none then begin_block INCONSISTENT 0
                               else if state = left orelse state = uvar then
                                   (add_string "("; begin_block INCONSISTENT 0)
                               else ();
                               pppretype left ty1;
                               add_string " +";
                               pp_if_prerank (Prekind.prank_of Kind);
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
         | TyExis(tyv, ty) => (add_string "(?";
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
                               pp_prekind Kind;
                               end_block())
         | TyRankConstr {Ty, Rank} =>
                              (begin_block INCONSISTENT 0;
                               pppretype none Ty;
                               add_string " :<=";
                               add_break(1,2);
                               pp_prerank Rank;
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


(*---------------------------------------------------------------------------*
 * Calculate the prekind or prerank of a pretype.                            *
 *---------------------------------------------------------------------------*)

val op ==> = Prekind.==>

local
  open Prekind Prerank
  val zero = Zerorank
  val inc  = Sucrank
  val max  = mk_Maxrank
in
fun pkind_of0 (Vartype(s,kd)) = kd
  | pkind_of0 (Contype{Kind, ...}) = Kind
  | pkind_of0 (TyApp(opr,arg)) = (Prekind.chase (pkind_of opr)
                                  handle e as HOL_ERR _ =>
                                  (print ("Type application of type operator\n" ^ pretype_to_string opr ^
                                          "\nto type argument\n" ^ pretype_to_string arg ^
                                          "failed in pkind_of0 by chase exception\n");
                                   raise (wrap_exn "Pretype.pkind_of"
                                      (pretype_to_string (PT(TyApp(opr,arg),locn.Loc_None))) e)))
  | pkind_of0 (ty as TyUniv _) = typ (prank_of0 ty) (* NOT pkind_of body *)
  | pkind_of0 (ty as TyExis _) = typ (prank_of0 ty) (* NOT pkind_of body *)
  | pkind_of0 (TyAbst(Bvar,Body)) = pkind_of Bvar ==> pkind_of Body
  | pkind_of0 (TyKindConstr{Ty,Kind}) = Kind
  | pkind_of0 (TyRankConstr{Ty,Rank}) = pkind_of Ty
  | pkind_of0 (UVar (ref (NONEU kd))) = kd
  | pkind_of0 (UVar (ref (SOMEU ty))) = pkind_of ty
and pkind_of (pty as PT(ty,locn)) = pkind_of0 ty

and prank_of0 (TyUniv(Bvar,Body))     = max(inc(prank_of_type Bvar), prank_of_type Body)
  | prank_of0 (TyExis(Bvar,Body))     = max(inc(prank_of_type Bvar), prank_of_type Body)
  | prank_of0 (TyRankConstr{Ty,Rank}) = Rank
  | prank_of0 (UVar (ref (SOMEU ty))) = prank_of_type ty
  | prank_of0 ty                      = prank_of (pkind_of0 ty)
and prank_of_type (PT(ty,locn)) = prank_of0 ty
end;


fun ((ty1 as PT(_,loc1)) --> (ty2 as PT(_,loc2))) =
  let val max = Prerank.mk_Maxrank
      val rank = max(prank_of_type ty1, prank_of_type ty2)
                 handle Fail _    => (* prank_of can fail if types not yet checked *)
                 Prerank.new_uvar()
                 handle HOL_ERR _ => (* prank_of can fail if types not yet checked *)
                 Prerank.new_uvar()
      val kind = Prekind.typ rank
  in
    PT(TyApp(PT(TyApp(PT(Contype {Thy = "min", Tyop = "fun",
                                  Kind = kind ==> kind ==> kind},
                         locn.Loc_None),
                      ty1),
                locn.Loc_None),
             ty2),
       locn.between loc1 loc2)
  end

fun mk_exist_type(ty1 as PT(_,loc1), ty2 as PT(_,loc2)) =
    PT(TyExis(ty1,ty2), locn.between loc1 loc2)

(* dest_exist_type is defined below after the definition of beta conversion. *)
fun dest_exist_type0(PT(UVar(ref(SOMEU ty)),loc)) = dest_exist_type0 ty
  | dest_exist_type0(PT(TyKindConstr{Ty,Kind},loc)) = dest_exist_type0 Ty
  | dest_exist_type0(PT(TyRankConstr{Ty,Rank},loc)) = dest_exist_type0 Ty
  | dest_exist_type0(ty as PT(TyExis(ty1,ty2),loc)) = (ty1,ty2)
  | dest_exist_type0 _ = raise TCERR "dest_exist_type" "not an existential type";

val is_exist_type = can dest_exist_type0



(*---------------------------------------------------------------------------*
 *    Section on substitution.                                               *
 *---------------------------------------------------------------------------*)

fun apply_subst subst (pt as PT (pty, locn)) =
  case pty of
    Vartype _ => pt
  | Contype _ => pt
  | TyApp(ty1, ty2) => PT (TyApp(apply_subst subst ty1, apply_subst subst ty2), locn)
  | TyUniv(bty, body) => PT (TyUniv(apply_subst subst bty, apply_subst subst body), locn)
  | TyExis(bty, body) => PT (TyExis(apply_subst subst bty, apply_subst subst body), locn)
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
 * Given a type variable and a list of type variables, if the type variable  *
 * does not exist on the list, then return the type variable. Otherwise,     *
 * rename the type variable and try again. Note well that the variant uses   *
 * only the name of the variable as a basis for testing equality. Experience *
 * has shown that basing the comparison on all of the name, the arity, the   *
 * rank, and the type arguments of the variable resulted in needlessly       *
 * confusing formulas occasionally being displayed in interactive sessions.  *
 *---------------------------------------------------------------------------*)

fun gen_variant caller =
  let fun var_name (PT(Vartype(Name,_),_)) = Name
        | var_name _ = raise TCERR caller "not a variable"
      fun vary vlist (PT(Vartype(Name,Kind),locn)) =
          let val L = map var_name (filter is_var_type vlist)
              val next = Lexis.gen_variant Lexis.tyvar_vary L
              fun loop name =
                 let val s = if mem name L then next name else name
                 in s
                 end
          in PT(Vartype(loop Name, Kind),locn)
          end
        | vary _ _ = raise TCERR caller "2nd argument should be a variable"
  in vary
  end;

fun variant_type fvs v = if is_var_type v then gen_variant "variant_type" fvs v
                            else (* v is a uvar *)
                            if op_mem eq v fvs then new_uvar(pkind_of v)
                            else v


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
          | vsubs0 fmap (v as UVar (ref(NONEU _))) =
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
          | vsubs0 fmap (TyExis(Bvar,Body)) =
               let val Bvar1 = the_var_type Bvar
                   val fmap = delete(fmap,Bvar1)
                   val frees = type_vars_subst fmap
                   val fvs = Lib.op_set_diff eq (type_vars Body) [Bvar1]
                   val Bvar' = variant_type (Lib.op_union eq frees fvs) Bvar1
               in if eq Bvar1 Bvar' then TyExis(Bvar, vsubs fmap Body)
                  else let val fmap' = insert(fmap,Bvar1,Bvar')
                       in TyExis(vsubs fmap' Bvar, vsubs fmap' Body)
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
                 | TyExis(Bvar,Body) =>
                     let val Bvar1 = the_var_type Bvar
                         val frees = type_vars_subst fmap
                         val fvs = Lib.op_set_diff eq (type_vars Body) [Bvar1]
                         val Bvar' = variant_type (Lib.op_union eq frees fvs) Bvar1
                     in if eq Bvar1 Bvar' then PT(TyExis(Bvar, subs fmap Body), locn)
                        else let val fmap' = insert(fmap,Bvar1,Bvar')
                             in PT(TyExis(subs fmap' Bvar, subs fmap' Body), locn)
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
          | dbvs0 cxvs (TyExis(Bvar,Body)) =
               let val Bvar1 = the_var_type Bvar
                   val fvs = Lib.op_set_diff eq (type_vars Body) [Bvar1]
                   val Bvar' = variant_type (Lib.op_union eq cxvs fvs) Bvar1
                   val cxvs' = Bvar'::cxvs
               in if eq Bvar1 Bvar' then TyExis(Bvar, dbvs cxvs' Body)
                  else let val instfn = type_subst [Bvar1 |-> Bvar']
                       in TyExis(instfn Bvar, dbvs cxvs' (instfn Body))
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
val EERR = TCERR "eta_conv_ty" "not a type eta redex"
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
val BERR = TCERR "beta_conv_ty" "not a type beta redex"
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
             val _ = Prekind.unify_le (pkind_of N) (* :<=: *) (pkind_of Bvar);
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
           ["rand_conv_ty", "rator_conv_ty", "abs_conv_ty", "univ_conv_ty", "exist_conv_ty", "uvar_conv_ty"]
         andalso origin_structure = "Pretype"
      then
        raise TCERR "rand_conv_ty" message
      else
        raise TCERR "rand_conv_ty" (origin_function ^ ": " ^ message)
in
  PT(TyApp(Rator, Newrand), locn)
end
  | rand_conv_ty conv _ = raise TCERR "rand_conv_ty" "not a pretype application"

(* ---------------------------------------------------------------------*)
(* rator_conv_ty conv ``:t2 t1`` applies conv to t1                     *)
(* ---------------------------------------------------------------------*)

fun rator_conv_ty conv (PT(TyApp(Rator,Rand), locn)) = let
  val Newrator = conv Rator
    handle HOL_ERR {origin_function, message, origin_structure} =>
      if Lib.mem origin_function
           ["rand_conv_ty", "rator_conv_ty", "abs_conv_ty", "univ_conv_ty", "exist_conv_ty", "uvar_conv_ty"]
         andalso origin_structure = "Pretype"
      then
        raise TCERR "rator_conv_ty" message
      else
        raise TCERR "rator_conv_ty" (origin_function ^ ": " ^ message)
in
  PT(TyApp(Newrator, Rand), locn)
end
  | rator_conv_ty conv _ = raise TCERR "rator_conv_ty" "not a pretype application"

(* ----------------------------------------------------------------------
    abs_conv_ty conv ``: \'a. t['a]`` applies conv to t['a]
   ---------------------------------------------------------------------- *)

fun abs_conv_ty conv (PT(TyAbst(Bvar,Body), locn)) = let
  val Newbody = conv Body
    handle HOL_ERR {origin_function, message, origin_structure} =>
      if Lib.mem origin_function
           ["rand_conv_ty", "rator_conv_ty", "abs_conv_ty", "univ_conv_ty", "exist_conv_ty", "uvar_conv_ty"]
         andalso origin_structure = "Pretype"
      then
        raise TCERR "abs_conv_ty" message
      else
        raise TCERR "abs_conv_ty" (origin_function ^ ": " ^ message)
in
  PT(TyAbst(Bvar, Newbody), locn)
end
  | abs_conv_ty conv _ = raise TCERR "abs_conv_ty" "not a pretype abstraction"

(* ----------------------------------------------------------------------
    kind_constr_conv_ty conv ``: t : k`` applies conv to t
   ---------------------------------------------------------------------- *)

fun kind_constr_conv_ty conv (PT(TyKindConstr{Ty,Kind}, locn)) = let
  val Newty = conv Ty
    handle HOL_ERR {origin_function, message, origin_structure} =>
      if Lib.mem origin_function
           ["rand_conv_ty", "rator_conv_ty", "abs_conv_ty", "univ_conv_ty", "exist_conv_ty", "uvar_conv_ty"]
         andalso origin_structure = "Pretype"
      then
        raise TCERR "kind_constr_conv_ty" message
      else
        raise TCERR "kind_constr_conv_ty" (origin_function ^ ": " ^ message)
in
  PT(TyKindConstr{Ty=Newty,Kind=Kind}, locn)
end
  | kind_constr_conv_ty conv _ = raise TCERR "kind_constr_conv_ty" "not a pretype kind constraint"

(* ----------------------------------------------------------------------
    rank_constr_conv_ty conv ``: t : k`` applies conv to t
   ---------------------------------------------------------------------- *)

fun rank_constr_conv_ty conv (PT(TyRankConstr{Ty,Rank}, locn)) = let
  val Newty = conv Ty
    handle HOL_ERR {origin_function, message, origin_structure} =>
      if Lib.mem origin_function
           ["rand_conv_ty", "rator_conv_ty", "abs_conv_ty", "univ_conv_ty", "exist_conv_ty", "uvar_conv_ty"]
         andalso origin_structure = "Pretype"
      then
        raise TCERR "rank_constr_conv_ty" message
      else
        raise TCERR "rank_constr_conv_ty" (origin_function ^ ": " ^ message)
in
  PT(TyRankConstr{Ty=Newty,Rank=Rank}, locn)
end
  | rank_constr_conv_ty conv _ = raise TCERR "rank_constr_conv_ty" "not a pretype rank constraint"

(* ----------------------------------------------------------------------
    univ_conv_ty conv ``: !'a. t['a]`` applies conv to t['a]
   ---------------------------------------------------------------------- *)

fun univ_conv_ty conv (PT(TyUniv(Bvar,Body), locn)) = let
  val Newbody = conv Body
    handle HOL_ERR {origin_function, message, origin_structure} =>
      if Lib.mem origin_function
           ["rand_conv_ty", "rator_conv_ty", "abs_conv_ty", "univ_conv_ty", "exist_conv_ty", "uvar_conv_ty"]
         andalso origin_structure = "pretype"
      then
        raise TCERR "univ_conv_ty" message
      else
        raise TCERR "univ_conv_ty" (origin_function ^ ": " ^ message)
in
  PT(TyUniv(Bvar, Newbody), locn)
end
  | univ_conv_ty conv _ = raise TCERR "univ_conv_ty" "not a universal pretype"

(* ----------------------------------------------------------------------
    exist_conv_ty conv ``: ?'a. t['a]`` applies conv to t['a]
   ---------------------------------------------------------------------- *)

fun exist_conv_ty conv (PT(TyExis(Bvar,Body), locn)) = let
  val Newbody = conv Body
    handle HOL_ERR {origin_function, message, origin_structure} =>
      if Lib.mem origin_function
           ["rand_conv_ty", "rator_conv_ty", "abs_conv_ty", "univ_conv_ty", "exist_conv_ty", "uvar_conv_ty"]
         andalso origin_structure = "pretype"
      then
        raise TCERR "exist_conv_ty" message
      else
        raise TCERR "exist_conv_ty" (origin_function ^ ": " ^ message)
in
  PT(TyExis(Bvar, Newbody), locn)
end
  | exist_conv_ty conv _ = raise TCERR "exist_conv_ty" "not an existential pretype"

(* ----------------------------------------------------------------------
    uvar_conv_ty conv (Uvar (SOMEU ty)) applies conv to ty
   ---------------------------------------------------------------------- *)

fun uvar_conv_ty conv (PT(UVar (r as ref (SOMEU ty)), locn)) = let
  val Newty = conv ty
    handle HOL_ERR {origin_function, message, origin_structure} =>
      if Lib.mem origin_function
           ["rand_conv_ty", "rator_conv_ty", "abs_conv_ty", "univ_conv_ty", "exist_conv_ty", "uvar_conv_ty"]
         andalso origin_structure = "Pretype"
      then
        raise TCERR "uvar_conv_ty" message
      else
        raise TCERR "uvar_conv_ty" (origin_function ^ ": " ^ message)
in
  (* Newty *)
  PT(UVar (ref (SOMEU Newty)), locn) (* creates a new reference to hold the converted value *)
end
  | uvar_conv_ty conv (ty as PT(UVar (ref (NONEU _)), locn)) = raise UNCHANGEDTY (* unchanged *)
  | uvar_conv_ty conv _ = raise TCERR "uvar_conv_ty" "not a pretype unification var"

(*---------------------------------------------------------------------------
 * Conversion that always fails;  identity element for orelse_ty.
 *---------------------------------------------------------------------------*)

fun no_conv_ty _ = raise TCERR "no_conv_ty" "";

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
   handle HOL_ERR _ => raise TCERR "every_conv_ty" "";


(*---------------------------------------------------------------------------
 * Cause the conversion to fail if it does not change its input.
 *---------------------------------------------------------------------------*)

fun changed_conv_ty conv ty =
   let val ty1 = conv ty
           handle UNCHANGEDTY => raise TCERR "changed_conv_ty" "Input type unchanged"
   in if eq ty ty1 then raise TCERR"changed_conv_ty" "Input type unchanged"
      else ty1
   end;

(* ----------------------------------------------------------------------
    Cause a failure if the conversion causes the UNCHANGED exception to
    be raised.  Doesn't "waste time" doing an equality check.  Mnemonic:
    "quick changed_conv".
   ---------------------------------------------------------------------- *)

fun qchanged_conv_ty conv ty =
    conv ty
    handle UNCHANGEDTY => raise TCERR "qchanged_conv_ty" "Input type unchanged"

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
  | app_conv_ty conv _ = raise TCERR "app_conv_ty" "not a pretype application"

fun sub_conv_ty conv =
    try_conv_ty (app_conv_ty conv orelse_ty abs_conv_ty conv
                 orelse_ty univ_conv_ty conv orelse_ty exist_conv_ty conv
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
  | head_beta1_ty _ = raise TCERR "head_beta1_ty" "no beta redex found"

(*  head_beta_ty repeatedly reduces any head beta redexes; never fails *)
(*  result has at its top level its actual shape *)
val head_beta_ty = qconv_ty (repeat_ty head_beta1_ty)

fun is_abconv_env c1 c2 ty1 ty2 =
    eq_env c1 c2 (deep_beta_eta_ty ty1) (deep_beta_eta_ty ty2)
fun all_abconv_env c1 c2 (ty1::tys1) (ty2::tys2) =
    is_abconv_env c1 c2 ty1 ty2 andalso all_abconv_env c1 c2 tys1 tys2
  | all_abconv_env c1 c2 [] [] = true
  | all_abconv_env c1 c2 anything other = false
fun is_abconv ty1 ty2 = is_abconv_env [] [] ty1 ty2
fun all_abconv tys1 tys2 = all_abconv_env [] [] tys1 tys2


val dest_univ_type = dest_univ_type0 o deep_beta_eta_ty
val dest_exist_type = dest_exist_type0 o deep_beta_eta_ty

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

fun strip_exist_type ty =
    let fun strip ty =
       let val (bvar, body1) = dest_exist_type0 ty
           val (bvars, body) = strip body1
       in (bvar::bvars, body)
       end
       handle HOL_ERR _ => ([],ty)
    in strip (deep_beta_eta_ty ty)
    end

fun spaces n = if n = 0 then "" else ("  " ^ spaces(n-1))


infix ref_occurs_in

fun r ref_occurs_in (PT(value, locn)) =
  case value of
    Vartype _ => false
  | Contype _ => false
  | TyApp(ty1, ty2) => r ref_occurs_in ty1 orelse r ref_occurs_in ty2
  | TyUniv(tyv, ty) => r ref_occurs_in tyv orelse r ref_occurs_in ty
  | TyExis(tyv, ty) => r ref_occurs_in tyv orelse r ref_occurs_in ty
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
      UVar (ref (NONEU kd))    => Prekind.has_free_uvar kd
    | UVar (ref (SOMEU pty'))  => has_free_uvar_kind pty'
    | Vartype (_,kd)           => Prekind.has_free_uvar kd
    | Contype {Kind,...}       => Prekind.has_free_uvar Kind
    | TyApp(ty1, ty2)          => has_free_uvar_kind ty1 orelse has_free_uvar_kind ty2
    | TyAbst(tyv, ty)          => has_free_uvar_kind tyv orelse has_free_uvar_kind ty
    | TyUniv(tyv, ty)          => has_free_uvar_kind tyv orelse has_free_uvar_kind ty
    | TyExis(tyv, ty)          => has_free_uvar_kind tyv orelse has_free_uvar_kind ty
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
    | TyExis(tyv, ty)         => has_free_uvar tyv orelse has_free_uvar ty
    | TyKindConstr {Ty, ...}  => has_free_uvar Ty
    | TyRankConstr {Ty, ...}  => has_free_uvar Ty


fun kind_unify n k1 k2 (rk_env,kd_env,ty_env) =
  let val ((rk_env',kd_env'), result) = Prekind.unsafe_unify n k1 k2 (rk_env,kd_env)
  in ((rk_env',kd_env',ty_env), result)
  end

fun kind_unify_le n k1 k2 (rk_env,kd_env,ty_env) =
  let val ((rk_env',kd_env'), result) = Prekind.unsafe_unify_le n k1 k2 (rk_env,kd_env)
  in ((rk_env',kd_env',ty_env), result)
  end

fun conty_kind_unify n k1 k2 (rk_env,kd_env,ty_env) =
  let val ((rk_env',kd_env'), result) = Prekind.unsafe_conty_unify n k1 k2 (rk_env,kd_env)
  in ((rk_env',kd_env',ty_env), result)
  end

fun rank_unify n r1 r2 (rk_env,kd_env,ty_env) =
  let val (rk_env', result) = Prerank.unsafe_unify n r1 r2 rk_env
  in if not (is_debug()) then () else
     case result of SOME _ => () | NONE =>
         (print "\nrank_unify failed:\n";
          print (Prerank.prerank_to_string r1 ^ "\n" ^ spaces n ^ "compared to\n" ^
                 Prerank.prerank_to_string r2 ^ "\n"));
     ((rk_env',kd_env,ty_env), result)
  end

fun deref (env as (rk_env,kd_env,ty_env)) (ty as PT(ty0,loc0)) =
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
        | TV (PT(TyExis(v,ty),_)) E B A k   = TV ty E (insert v B) A k
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


local
fun str [(s,_)] = s
  | str ((s,_)::cs) = str cs ^ "," ^ s
  | str [] = ""
in
fun env_to_string cs =
  if null cs then ""
  else "[" ^ str cs ^ "] |- "
end

(* Global variables for current error reporter and hom list *)

val error_report         = ref ("", fn e:exn => ()) (* set by Preterm as context of current unifications *)
val current_error_report = ref ("", fn e:exn => ()) (* set when processing a hom for error handling *)
fun get_error_report () = !error_report
fun set_error_report f = (error_report := f; ())

fun report s cmp n c1 c2 ty1 ty2 m e =
  let val _ = if not (is_debug()) then () else
          print ("\n" ^ spaces n ^ s ^ ": " ^
                 env_to_string c1 ^
                 pretype_to_string ty1 ^ "\n" ^
                 spaces n ^ "to be   " ^ cmp ^ "    to: " ^
                 env_to_string c2 ^
                 pretype_to_string ty2 ^ "\n")
      val (e',result) = m e
  in case result
       of NONE => if not (is_debug()) then () else
                  (print ("\n" ^ spaces n ^ s ^ " failed for\n" ^ spaces n);
                   print (env_to_string c1 ^ pretype_to_string ty1 ^ "\n" ^ spaces n ^ "compared to\n" ^ spaces n);
                   print (env_to_string c2 ^ pretype_to_string ty2 ^ "\n"))
      | SOME() => if not (is_debug()) then () else
                  (print ("\n" ^ spaces n ^ s ^ " succeeded for\n" ^ spaces n);
                   print (env_to_string c1 ^ pretype_to_string ty1 ^ "\n" ^ spaces n ^ "compared to\n" ^ spaces n);
                   print (env_to_string c2 ^ pretype_to_string ty2 ^ "\n"));
      (e',result)
  end


fun mk_vartype tv = PT(Vartype tv, locn.Loc_None)
fun shift_context c1 c2 =
  let val theta = map (fn (tv1,tv2) => mk_vartype tv1 |-> mk_vartype tv2) (zip c1 c2)
  in type_subst theta
  end
val mk_uvs = map (fn arg => PT(UVar(ref(NONEU (pkind_of arg))), locn.Loc_None))

fun inc_report f x =
  let val n = current_trace "debug_type_inference"
      val _ = set_trace "debug_type_inference" (n + 1)
      val r = f x
      val _ = set_trace "debug_type_inference" n
  in r
  end

fun unsafe_bind n f c1 c2 r value =
inc_report (report "Bind type uvar " "=" n c1 c2 (PT(UVar r, locn.Loc_None)) value (fn env => (
(* print ("\nBind type uvar " ^ pretype_to_string (PT(UVar r, locn.Loc_None)) ^ " to\n"
       ^ pretype_to_string value ^ "\n"); *)
  if r ref_equiv value
  then ok
  else if r ref_occurs_in value orelse isSomeU (!r)
       then fail
       else
         (fn (rk_env,kd_env,acc) =>
             (((rk_env,kd_env,(r, !r)::acc), SOME ())
              before r := SOMEU (shift_context c2 c1 value)))
) env))


type homatch = bool (*lep*) * int (*n*)
                   * pretyvar list * pretyvar list * pretype * pretype
                   * (string * (exn -> unit))

fun hom_str0 ((lep, n, c1, c2, ty1, ty2, erpt):homatch) =
       env_to_string c1 ^
       pretype_to_string (deep_beta_eta_ty ty1) ^ "\n " ^
       (if lep then "<=" else " =") ^ " compared to\n" ^
       env_to_string c2 ^
       pretype_to_string (deep_beta_eta_ty ty2) ^ "\n";

fun hom_str ((lep, n, c1, c2, ty1, ty2, erpt):homatch) =
       hom_str0 (lep, n, c1, c2, ty1, ty2, erpt) ^
       "This h.o. match is for the term\n" ^ fst erpt ^ "\n";

fun homs_str0 n (h::hs) = "\ncurrent h.o. match #" ^ Int.toString n ^ ":\n" ^
                          hom_str0 h ^ "\n" ^ homs_str0 (n+1) hs
  | homs_str0 n [] = ""
fun homs_str hs = homs_str0 1 hs

val homs = ref ([[]] : homatch list list);
fun begin_homs()  = ( (*print "Beginning homs.\n"; *)
                     homs := [] :: (!homs); ())
fun get_homs ()   = hd (!homs);
fun get_all_homs()= flatten (!homs);
fun dest_homs c = case !homs of hs1::rst => (hs1,rst)
                               | _ => raise TCERR c "empty homs stack"
fun reset_homs () = let val (hs1,rst) = dest_homs "reset_homs"
                        val len = length hs1
                    in
                      if len = 0 then () else
                        if not (ho_debug()) then () else
                          print ("\nHarvesting " ^ Int.toString len ^ " homs.\n");
                      homs := []::rst; hs1 end;
fun add_hom h     = let val (hs1,rst) = dest_homs "add_hom"
                        val (lep,n,c1,c2,ty1,ty2) = h
                        val h' = (lep,n,c1,c2,ty1,ty2,get_error_report())
                    in
                      if not (ho_debug()) then () else
                        print ("\nAdding hom #" ^ Int.toString(length hs1 + 1) ^ ":\n" ^
                               hom_str h');
                      homs := (h'::hs1)::rst; () end;
fun end_homs ()   = let val (hs1,rst) = dest_homs "end_homs"
                    in
                      (* print "Ending homs.\n\n"; *)
                      if null hs1 then () else
                        if not (ho_debug()) then () else
                          print ("\nDropping " ^ Int.toString (length hs1) ^ " homs.\n");
                      homs := rst; hs1 end;
local
  val MAX = 1000
  fun measure_type ty ty' =
    let val (opr,args) = strip_app_type ty
    in
      if not (null args) andalso
         has_var_type opr andalso is_uvar_type(the_var_type opr)
      then if all has_real_var_type args
           then if distinct_vars args
                then if not (contains_uvar_type ty') (* prefer no uvars *)
                     then MAX - length args (* prefer short argument lists *)
                     else 5
                else 4
           else if contains_uvar_typel args
                then 2
                else 3
      else if contains_uvar_type opr
           then 1
           else 0
    end
  fun measure_hom (lep, n, c1, c2, ty1, ty2, erpt) =
    let val m1 = measure_type ty1 ty2
        val m2 = measure_type ty2 ty1
    in if m1 = 0 andalso m2 = 0
       then 10 (* structural match, not h.o. *)
       else Int.max(m1, m2)
    end
  fun index_max [m] = (0,m)
    | index_max (m::ms) =
        let val (i,mi) = index_max ms
        in if m >= mi then (0,m)
                      else (i+1,mi)
        end
    | index_max _ = raise TCERR "index_max" "empty measure list"
  fun pick_index 0 (h::hs) = (h, hs)
    | pick_index n (h::hs) =
        let val (h', hs') = pick_index (n-1) hs
        in (h', h::hs')
        end
    | pick_index _ _ = raise TCERR "pick_index" "empty hom list"
  fun measures_str _ [m] = Int.toString m
    | measures_str n (m::ms) = Int.toString m ^ "," ^
                              (if n mod 10 = 0 then "\n           " else "") ^
                               measures_str (n+1) ms
    | measures_str _ _ = raise TCERR "measures_str" "empty measures list"
in
fun select_hom (hs as _::_) =
    let val ms = map measure_hom hs
        val (i,m) = index_max ms
        val _ = if not (ho_debug()) then () else
                  print ("\nCurrent homs:\n" ^ homs_str hs ^
                         "Measures: [" ^ measures_str 1 ms ^
                                     "]; picking #" ^ Int.toString (i+1) ^
                                              " = " ^ Int.toString m ^ "\n")
    in SOME (pick_index i hs)
    end
  | select_hom _ = NONE
end

local
open Lib

(* with_nu_vars_is_not_univ_type1 is true iff the argument is decidedly NOT a universal type
   and does not contain a universal type,
   supposing that the uvars(NONE) referenced in nu_vars will never be universal types. *)
(* Such a type would clash if unified with a universal type. *)
fun with_nu_vars_is_not_univ_type nu_vars =
  let fun is_not_univ_type0(PT(UVar(ref(SOMEU ty)),_)) = is_not_univ_type0 ty
        | is_not_univ_type0(PT(UVar(r as ref(NONEU _ )),_)) = mem r nu_vars
        | is_not_univ_type0(PT(TyKindConstr{Ty,Kind},_)) = is_not_univ_type0 Ty
        | is_not_univ_type0(PT(TyRankConstr{Ty,Rank},_)) = is_not_univ_type0 Ty
        | is_not_univ_type0(PT(TyUniv(ty1,ty2),_)) = false
        | is_not_univ_type0(PT(TyExis(ty1,ty2),_)) = is_not_univ_type0 ty2
        | is_not_univ_type0(PT(TyAbst(ty1,ty2),_)) = is_not_univ_type0 ty2
        | is_not_univ_type0(PT(TyApp(ty1,ty2),_)) = is_not_univ_type0 ty1
        | is_not_univ_type0 _ = true
  in is_not_univ_type0
  end

fun non_univ_uvars_of_hom nu_vars (hom as (lep, n, c1, c2, ty1, ty2, erpt):homatch) =
  let val is_not_univ_type = with_nu_vars_is_not_univ_type nu_vars
      val (opr1,args1) = strip_app_type ty1
      val (opr2,args2) = strip_app_type ty2
      fun is_a_uvar ty = has_var_type ty andalso is_uvar_NONE_type (the_var_type ty)
      val res = subtract (union
                            (if is_a_uvar opr1
                                andalso is_not_univ_type opr2 (*ty2*)
                             then uvars_NONE_of opr1
                             else [])
                            (if is_a_uvar opr2
                                andalso is_not_univ_type opr1 (*ty1*)
                             then uvars_NONE_of opr2
                             else []))
                         nu_vars
  in
    res
  end
  fun recurse n nu_vars homs =
    let val new_nu_vars = U (map (non_univ_uvars_of_hom nu_vars) homs)
    in (*print ("\nFound in this pass #" ^ Int.toString n ^ ", " ^
                Int.toString (length new_nu_vars) ^ " new non-universal uvars.\n");*)
       if null new_nu_vars then nu_vars
       else recurse (n+1) (union nu_vars new_nu_vars) homs
    end
in
fun non_univ_hom_uvars () = recurse 1 [] (get_all_homs())
fun with_homs_is_not_univ_type ty =
      with_nu_vars_is_not_univ_type (non_univ_hom_uvars()) ty
end

fun new_hom h e = (add_hom h; return () e)



(* first argument is a function which performs a binding between a
   pretype reference and another pretype, updating some sort of environment
   (the 'a), returning the new alpha and a unit option, SOME () for a
   success, and a NONE, if not.

   To further complicate things, the bind argument also gets a copy of
   gen_unify to call, if it should choose.

   Also, all possible higher order matchings are added to the global variable
   "homs" to be processed later.  This variables needs to be set/reset externally.
*)
(* The environment "e" should be a triple:
     a rank environment CROSS a kind environment CROSS the type environment.  *)
(* this will need changing *)
(* eta-expansion *is* necessary *)
fun gen_unify (kind_unify   :int -> prekind -> prekind -> ('a -> 'a * unit option))
              (kind_unify_le:int -> prekind -> prekind -> ('a -> 'a * unit option))
              (conty_kind_unify:int -> prekind -> prekind -> ('a -> 'a * unit option))
              (rank_unify   :int -> prerank -> prerank -> ('a -> 'a * unit option))
              bind cmp tyvars n c1 c2 (ty1 as PT(t1,locn1)) (ty2 as PT(t2,locn2)) e = let
  val gen_unify = gen_unify kind_unify kind_unify_le conty_kind_unify rank_unify bind cmp tyvars (n+1)
  val kind_unify = kind_unify (n+1)
  val kind_unify_le = kind_unify_le (n+1)
  val conty_kind_unify = conty_kind_unify (n+1)
  val rank_unify = rank_unify (n+1)
  val bind = bind (n+1)
(*
  val ty1s = pretype_to_string ty1
  val ty2s = pretype_to_string ty2
  val ty1bs = pretype_to_string (deep_beta_eta_ty ty1)
  val ty2bs = pretype_to_string (deep_beta_eta_ty ty2)
  val _ = if is_debug() then print ("gen_unify " ^ ty1bs
                                ^ "\n      vs. " ^ ty2bs ^ "\n")
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
         rank_unify (prank_of_type ty) rk >> unify_var ty
    | unify_var (PT(UVar (r as ref (SOMEU ty)),_))  = unify_var ty
    | unify_var (ty as PT(UVar (ref (NONEU _)),_))  = return ty
    | unify_var (ty as PT(Vartype _,_))             = return ty
    | unify_var ty = (print ("unify_var fails on " ^ pretype_to_string ty ^ "\n"); fail)
  (* bvar_unify's inputs are reduced to either Vartype or UVar(NONEU),
     and then unified, returning the reduced types;
     the kinds must be unified to be eaual, not <=. *)
  fun bvar_unify ty1 (PT(UVar (r as ref (NONEU kd)),_)) =
         rank_unify (prank_of_type ty1) (Prekind.prank_of kd) >> (* ranks must = *)
         kind_unify (pkind_of ty1) kd >>
         bind gen_unify c2 c1 r ty1 >> 
         unify_var ty1 >- (fn ty1' => return (ty1',ty1'))
    | bvar_unify (PT(UVar (r as ref (NONEU kd)),_)) ty2 =
         rank_unify (Prekind.prank_of kd) (prank_of_type ty2) >> (* ranks must = *)
         kind_unify kd (pkind_of ty2) >>
         bind gen_unify c1 c2 r ty2 >>
         unify_var ty2 >- (fn ty2' => return (ty2',ty2'))
    | bvar_unify (ty1 as PT(Vartype (tv1 as (s1,kd1)),_))
                 (ty2 as PT(Vartype (tv2 as (s2,kd2)),_)) =
         rank_unify (Prekind.prank_of kd1) (Prekind.prank_of kd2) >> (* ranks must = *)
         kind_unify kd1 kd2 >> return (ty1,ty2)
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
  fun is_real_uvar_type ty =
        let val v = the_var_type ty
        in is_uvar_type v andalso
           let val vs = tyvars e v
           in length vs = 1 andalso eq v (hd vs)
           end
        end handle HOL_ERR _ => false
  fun match_var_type c1 c2 ty1 ty2 =
               is_real_uvar_type ty1
        orelse is_real_uvar_type ty2
        orelse eq_env c1 c2 ty1 ty2
  fun match_var_types c1 c2 [] [] = true
    | match_var_types c1 c2 (ty1::ty1s) (ty2::ty2s) = match_var_type c1 c2 ty1 ty2 andalso match_var_types c1 c2 ty1s ty2s
    | match_var_types _ _ _ _ = false
  fun match_eq_types c1 c2 [] [] = true
    | match_eq_types c1 c2 (ty1::ty1s) (ty2::ty2s) = eq_env c1 c2 ty1 ty2 andalso match_eq_types c1 c2 ty1s ty2s
    | match_eq_types _ _ _ _ = false
  fun vars_of ty = map the_var_type (tyvars e ty)
  fun vars_ofl tys = map the_var_type (foldl (fn (ty,tys) => Lib.union (tyvars e ty) tys) [] tys)
  fun uvars_of ty = filter is_uvar_type (vars_of ty)
  fun uvars_ofl tys = filter is_uvar_type (foldl (fn (ty,tys) => Lib.union (vars_of ty) tys) [] tys)
  fun all_uvars_real ty = all is_real_uvar_type (type_uvars ty)
  fun all_uvars_reall tys = all is_real_uvar_type (type_uvarsl tys)
  fun subset s1 s2 = all (fn v => op_mem eq v s2) s1
  fun mk_vs c1 c2 args = map (shift_context c1 c2) args
  val lep = (cmp = "<=")
in
report "Type unification" cmp n c1 c2 ty1 ty2 (
  case (t1, t2) of
(* Believe that kind_unify_le should be kind_unify (forcing equality),
   when binding a pretype UVar NONE to a value
   NO: this fails when constant c:(uv1:(ty:r1 => ty:r1) -> uv2:ty:r1)
       is applied to value v:('a:ty:r -> 'b:ty:0);
       uv2 is bound to 'b:ty:0, so r1 is bound to be equal to 0,
       but then uv1 is bound to 'a:ty:r, so r1(=0) must  be >= r. !!!
   Correction: for the third case below, it must be kind_unify, not kind_unify_le,
               so that the rank of the type uvar (r) does not decrease
   Correction: for the first case below, it must be kind_unify, not kind_unify_le,
               so that the rank of the type uvar (r) is equal to that of ty1   *)
    (_, UVar (r as ref (NONEU kd))) =>
        kind_unify_le (pkind_of ty1) (* :<=: (experimental) *) kd >>
        (*kind_unify(*_le*) (pkind_of ty1) (* :=: (experimental) *) kd >>*)
        bind gen_unify c2 c1 r ty1 (* (shift_context c1 c2 ty1) <-- error for safe bind *)
  | (_, UVar (r as ref (SOMEU ty2))) => gen_unify c1 c2 ty1 ty2
  | (UVar (r as ref (NONEU kd)), _) =>
        kind_unify_le kd (* :<=: *) (pkind_of ty2) >>
        (*kind_unify(*_le*) kd (* :=: *) (pkind_of ty2) >>*)
        bind gen_unify c1 c2 r ty2 (* (shift_context c2 c1 ty2) <-- error for safe bind *)
  | (UVar (r as ref (SOMEU ty1)), _) => gen_unify c1 c2 ty1 ty2
  | (Vartype (tv1 as (s1,kd1)), Vartype (tv2 as (s2,kd2))) =>
        (fn e => (if eq_varty c1 c2 tv1 tv2 then ok else fail) e) >>
            kind_unify_le kd1 kd2
  | (Contype {Kind=kd1,Thy=thy1,Tyop=tyop1},
     Contype {Kind=kd2,Thy=thy2,Tyop=tyop2}) =>
        (fn e => (if tyop1=tyop2 andalso thy1=thy2 then ok else fail) e) >>
            (*kind_unify_le*) conty_kind_unify kd1 kd2
  | (TyKindConstr{Ty=ty1',Kind=kd1}, _) =>
       kind_unify kd1 (pkind_of ty1') >> gen_unify c1 c2 ty1' ty2
  | (_, TyKindConstr{Ty=ty2',Kind=kd2}) =>
       kind_unify kd2 (pkind_of ty2') >> gen_unify c1 c2 ty1 ty2'
  | (TyRankConstr{Ty=ty1',Rank=rk1}, _) =>
       rank_unify rk1 (prank_of_type ty1') >> gen_unify c1 c2 ty1' ty2
  | (_, TyRankConstr{Ty=ty2',Rank=rk2}) =>
       rank_unify rk2 (prank_of_type ty2') >> gen_unify c1 c2 ty1 ty2'
  | (TyApp(ty11, ty12), TyApp(ty21, ty22)) =>
       if is_abs_type (head_ty ty11) then
           gen_unify c1 c2 (head_beta_ty ty1) ty2
       else if is_abs_type (head_ty ty21) then
            gen_unify c1 c2 ty1 (head_beta_ty ty2)
       else
       let val (opr1,args1) = strip_app_type ty1
           val (opr2,args2) = strip_app_type ty2
           val same_opr = length args1 = length args2 andalso eq_env c1 c2 opr1 opr2
           val simple = not same_opr andalso all_abconv_env c1 c2 args1 args2
           val var_match = not same_opr andalso not simple
                                        andalso match_var_types c1 c2 args1 args2
           val ho_1 = has_var_type opr1 andalso is_uvar_type(the_var_type opr1)
                                        andalso not same_opr
                                        andalso all_uvars_reall args1 andalso all_uvars_real ty2
                                        andalso not simple
                                        andalso (not var_match orelse
                                                  (let val uvars_ty2 = uvars_of ty2
                                                       val uvars_args1 = uvars_ofl args1
                                                   in subset uvars_ty2 uvars_args1
                                                      andalso subset uvars_args1 uvars_ty2
                                                   end))
                                     (* andalso not (match_eq_types c1 c2 args1 args2) *)
                                     (* andalso not (match_var_types c1 c2 args1 args2) *)
           val ho_2 = has_var_type opr2 andalso is_uvar_type(the_var_type opr2)
                                        andalso not same_opr
                                        andalso all_uvars_reall args2 andalso all_uvars_real ty1
                                        andalso not simple
                                        andalso (not var_match orelse
                                                  (let val uvars_ty1 = uvars_of ty1
                                                       val uvars_args2 = uvars_ofl args2
                                                   in subset uvars_ty1 uvars_args2
                                                      andalso subset uvars_args2 uvars_ty1
                                                   end))
                                     (* andalso not (match_eq_types c1 c2 args1 args2) *)
                                     (* andalso not (match_var_types c1 c2 args1 args2) *)
       in
          if ho_1 andalso (all has_var_type args1
                           orelse not (ho_2 andalso all has_var_type args2)) then
           (if not(is_debug()) then () else
               (print ("\n" ^ spaces n ^ "Higher order type unification on the left:\n"));
            if false andalso all has_var_type args1 andalso
               (let val uvars_ty2 = uvars_of ty2
                    val uvars_args1 = uvars_ofl args1
                in subset uvars_ty2 uvars_args1   (* ??? experimental *)
                   andalso subset uvars_args1 uvars_ty2
                end)
            then (* Higher order unification; shift args to other side by abstraction. *)
              let val vs = mk_vs c1 c2 args1
               in if list_eq vs args2
                  then gen_unify c1 c2 opr1 opr2
                  else gen_unify c1 c2 opr1 (list_mk_abs_type(vs,ty2))
              end
            else (* Higher order unification; solve this h.o. match later *)
              (new_hom(lep, n, c1, c2, ty1, ty2) >- (fn _ =>
               let val opr1_kd = Prekind.list_mk_arrow_kind(map pkind_of args1, pkind_of ty2)
                   val opr1' = new_uvar opr1_kd
               in
                 gen_unify c1 c1 opr1 opr1'
               end)))
          else if ho_2 then
           (if not(is_debug()) then () else
               (print ("\n" ^ spaces n ^ "Higher order type unification on the right:\n"));
            if false andalso all has_var_type args2 andalso
               (let val uvars_ty1 = uvars_of ty1
                    val uvars_args2 = uvars_ofl args2
                in subset uvars_ty1 uvars_args2   (* ??? experimental *)
                   andalso subset uvars_args2 uvars_ty1
                end)
            then (* Higher order unification; shift args to other side by abstraction. *)
              let val vs = mk_vs c2 c1 args2
               in if list_eq vs args1
                  then gen_unify c1 c2 opr1 opr2
                  else gen_unify c1 c2 (list_mk_abs_type(vs,ty1)) opr2
              end
            else (* Higher order unification; solve this h.o. match later *)
              (new_hom(lep, n, c1, c2, ty1, ty2) >- (fn _ =>
               let val opr2_kd = Prekind.list_mk_arrow_kind(map pkind_of args2, pkind_of ty1)
                   val opr2' = new_uvar opr2_kd
               in
                 gen_unify c2 c2 opr2' opr2
               end)))
          else if length args1 = length args2 then
               (* structural: unify arguments, in order, before operator *)
            mmap (fn (ty1,ty2) => gen_unify c1 c2 ty1 ty2) (zip args1 args2) >>
            gen_unify c1 c2 opr1 opr2
          else (* normal binary structural unification *)
            gen_unify c1 c2 ty11 ty21 >> gen_unify c1 c2 ty12 ty22 >> return ()
       end
  | (TyApp(ty11, ty12), _) =>
       if is_abs_type (head_ty ty11) then
           gen_unify c1 c2 (head_beta_ty ty1) ty2
       else
       let val (opr1,args1) = strip_app_type ty1
       in
         if has_var_type opr1 andalso is_uvar_type(the_var_type opr1) then
              (new_hom (lep, n, c1, c2, ty1, ty2) >- (fn _ =>
               let val opr1_kd = Prekind.list_mk_arrow_kind(map pkind_of args1, pkind_of ty2)
                   val opr1' = new_uvar opr1_kd
               in
                 gen_unify c1 c1 opr1 opr1'
               end))
         else fail (* normal structural unification *)
       end
  | (_, TyApp(ty21, ty22)) =>
       if is_abs_type (head_ty ty21) then
            gen_unify c1 c2 ty1 (head_beta_ty ty2)
       else
       let val (opr2,args2) = strip_app_type ty2
       in
         if has_var_type opr2 andalso is_uvar_type(the_var_type opr2) then
              (new_hom (lep, n, c1, c2, ty1, ty2) >- (fn _ =>
               let val opr2_kd = Prekind.list_mk_arrow_kind(map pkind_of args2, pkind_of ty1)
                   val opr2' = new_uvar opr2_kd
               in
                 gen_unify c2 c2 opr2' opr2
               end))
         else fail (* normal structural unification *)
       end
  | (TyUniv(ty11, ty12), TyUniv(ty21, ty22)) =>
         bvar_unify ty11 ty21 >- (fn (PT(ty11u,_),PT(ty21u,_)) =>
         case (ty11u,ty21u) of
            (Vartype tv1, Vartype tv2) =>
              gen_unify (tv1::c1) (tv2::c2) ty12 ty22
          | _ => gen_unify c1 c2 ty12 ty22)
  | (TyExis(ty11, ty12), TyExis(ty21, ty22)) =>
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
)
 end e

(* ho_match resolves higher-order matching problems as accumulated
   by gen_unify above.
   It can call gen_unify, which can generate more matching problems,
   but ho_match will also retrieve and solve those new problems,
   so one call to ho_match is sufficient.
   The gen_unify function used is the one saved with each problem.
*)
fun ho_match gen_unify gen_unify_le homs e = let
    val ho_match = ho_match gen_unify gen_unify_le
    fun collect_homs e =
             let val new_homs = reset_homs()
             in (e, SOME new_homs)
             end
    fun match leftp lep n c1 c2 (vty,vopr,vargs) (cty,copr,cargs) =
             let
               val gen_unify = if lep then gen_unify_le else gen_unify
               fun unify ty1 ty2 =
                 if leftp then gen_unify (n+1) c1 c2 ty1 ty2
                          else gen_unify (n+1) c2 c1 ty2 ty1
               val pats = map (shift_context c1 c2) vargs
             in
               if not (ho_debug()) then () else
               print ("\nmatch " ^ (if leftp then "left " else "right") ^ "\n" ^
                      env_to_string c1 ^
                      pretype_to_string vty ^ "\n " ^
                      (if lep then if leftp then "<=" else ">=" else " =") ^
                      " with\n" ^
                      env_to_string c2 ^
                      pretype_to_string cty ^ "\n");
               if all_abconv_env c1 c2 vargs cargs then
                 if eq copr vopr then
                   (if not (ho_debug()) then () else print "Satisfied\n"; ok)
                 else (* bind vopr to copr *)
                   (if not (ho_debug()) then () else
                      print ("Bind " ^ pretype_to_string vopr ^ " := " ^
                                       pretype_to_string copr ^ "\n");
                    unify vopr copr)
               else let
                   val ginsts = map (fn p => (p |->
                                                (if is_var_type p then p
                                                 else new_uvar(pkind_of p))))
                                    pats
                   val cty' = type_subst ginsts cty
                   val gvs = map #residue ginsts
                   val absty = list_mk_abs_type(gvs,cty')
                 in (* bind vopr to absty *)
                   if not (ho_debug()) then () else
                     print ("Bind " ^ pretype_to_string vopr ^ " := " ^
                                      pretype_to_string absty ^ "\n");
                   unify vopr absty
                 end
             end
  in
    case select_hom homs of
      NONE => ok
    | SOME (hom as (lep, n, c1, c2, ty1 as PT(t1,locn1), ty2 as PT(t2,locn2), erpt), rest_homs) =>
      let
        val _ = current_error_report := erpt
        val gen_unify = (if lep then gen_unify_le else gen_unify) (n+1)
        val cmp = if lep then "<=" else " ="
      in
report "H.O. type unification" cmp n c1 c2 ty1 ty2 (
      case (t1,t2) of
        (TyApp(ty11, ty12), TyApp(ty21, ty22)) =>
        if is_abs_type (head_ty ty11) then
            ho_match ((lep, n, c1, c2, head_beta_ty ty1, ty2, erpt) :: rest_homs)
        else if is_abs_type (head_ty ty21) then
            ho_match ((lep, n, c1, c2, ty1, head_beta_ty ty2, erpt) :: rest_homs)
        else
        let
            val _ = if not (ho_debug()) then () else
                      print ("\nProcessing hom #" ^ Int.toString(length rest_homs + 1) ^ ":\n" ^
                             hom_str hom)
            val (opr1,args1) = strip_app_type ty1
            val (opr2,args2) = strip_app_type ty2
            val same_opr = length args1 = length args2 andalso eq_env c1 c2 opr1 opr2
            val simple = all_abconv_env c1 c2 args1 args2
            (* if there are any UVar(NONE) variables in the arguments, don't h.o. match *)
            val ho_1 = has_var_type opr1 andalso is_uvar_type(the_var_type opr1)
                                         andalso not same_opr andalso not simple
                                         andalso not (contains_uvar_typel args1)
            val ho_2 = has_var_type opr2 andalso is_uvar_type(the_var_type opr2)
                                         andalso not same_opr andalso not simple
                                         andalso not (contains_uvar_typel args2)
            val all_vars1 = all has_var_type args1
            val all_vars2 = all has_var_type args2
            val leftp = ho_1 andalso
                          if all_vars1 then
                            distinct_vars args1 orelse
                              not (ho_2 andalso all_vars2 andalso distinct_vars args2)
                          else
                            not (ho_2 andalso all_vars2)
        in
          if leftp (* true iff matching left side, ty1, as h.o. *) then
            (if not (ho_debug()) then () else
                  print "Higher order unification on the left\n";
             match true lep n c1 c2 (ty1,opr1,args1) (ty2,opr2,args2) >>
             collect_homs >- (fn new_homs =>
             ho_match (new_homs @ rest_homs)))
          else if ho_2 then
            (if not (ho_debug()) then () else
                  print "Higher order unification on the right\n";
             match false lep n c2 c1 (ty2,opr2,args2) (ty1,opr1,args1) >>
             collect_homs >- (fn new_homs =>
             ho_match (new_homs @ rest_homs)))
          else if length args1 = length args2 then (* arguments, in order, before operator *)
            (if not (ho_debug()) then () else
                  print "Structural unification: arguments (in order), then operators\n";
             mmap (fn (ty1,ty2) => gen_unify c1 c2 ty1 ty2) (zip args1 args2) >>
             gen_unify c1 c2 opr1 opr2 >>
             collect_homs >- (fn new_homs =>
             ho_match (new_homs @ rest_homs)))
          else (* normal structural unification *)
            (if not (ho_debug()) then () else
                  print "Binary structural unification: operators then arguments\n";
             gen_unify c1 c2 ty11 ty21 >> gen_unify c1 c2 ty12 ty22 >>
             collect_homs >- (fn new_homs =>
             ho_match (new_homs @ rest_homs)))
        end

      | (TyApp(ty11, ty12), _) =>
        if is_abs_type (head_ty ty11) then
            ho_match ((lep, n, c1, c2, head_beta_ty ty1, ty2, erpt) :: rest_homs)
        else
        let
            val _ = if not (ho_debug()) then () else
                      print ("\nProcessing hom #" ^ Int.toString(length rest_homs + 1) ^ ":\n" ^
                             hom_str hom)
            val (opr1,args1) = strip_app_type ty1
            (* if there are any UVar(NONE) variables in the arguments, don't h.o. match *)
            val ho_1 = has_var_type opr1 andalso is_uvar_type(the_var_type opr1)
                                         andalso not (contains_uvar_typel args1)
        in
          if ho_1 then
             match true lep n c1 c2 (ty1,opr1,args1) (ty2,ty2,[]) >>
             collect_homs >- (fn new_homs =>
             ho_match (new_homs @ rest_homs))
          else
            (* normal structural unification *)
            case t2 of
              TyUniv(bv, body) =>
                (* Assume an unperceived missing type argument *)
                let val newbv = new_uvar(pkind_of bv)
                    val body' = type_subst [bv |-> newbv] body
                in ho_match ((lep, n, c1, c2, ty1, body', erpt) :: rest_homs)
                end
            | _ => fail
        end

      | (_, TyApp(ty21, ty22)) =>
        if is_abs_type (head_ty ty21) then
            ho_match ((lep, n, c1, c2, ty1, head_beta_ty ty2, erpt) :: rest_homs)
        else
        let
            val _ = if not (ho_debug()) then () else
                      print ("\nProcessing hom #" ^ Int.toString(length rest_homs + 1) ^ ":\n" ^
                             hom_str hom)
            val (opr2,args2) = strip_app_type ty2
            (* if there are any UVar(NONE) variables in the arguments, don't h.o. match *)
            val ho_2 = has_var_type opr2 andalso is_uvar_type(the_var_type opr2)
                                         andalso not (contains_uvar_typel args2)
        in
          if ho_2 then
             match false lep n c2 c1 (ty2,opr2,args2) (ty1,ty1,[]) >>
             collect_homs >- (fn new_homs =>
             ho_match (new_homs @ rest_homs))
          else
            (* normal structural unification *)
            case t1 of
              TyUniv(bv, body) =>
                (* Assume an unperceived missing type argument *)
                let val newbv = new_uvar(pkind_of bv)
                    val body' = type_subst [bv |-> newbv] body
                in ho_match ((lep, n, c1, c2, body', ty2, erpt) :: rest_homs)
                end
            | _ => fail
        end

      | (_, _) =>
            (if not (ho_debug()) then () else
                      print ("\nProcessing hom #" ^ Int.toString(length rest_homs + 1) ^ ":\n" ^
                             hom_str hom);
             if not (ho_debug()) then () else
                  print "Handle by general unification.\n";
             gen_unify c1 c2 ty1 ty2 >>
             collect_homs >- (fn new_homs =>
             ho_match (new_homs @ rest_homs)))
)
      end handle e as HOL_ERR _ =>
        (if not (ho_debug()) then () else
                 print ("\nProcessing hom #" ^ Int.toString(length rest_homs + 1) ^ " failed:\n" ^
                             hom_str hom);
         raise e)
  end e



val empty_env = ([]:(oprerank option ref * oprerank option) list,
                 []:(uvarkind ref * uvarkind) list,
                 []:(uvartype ref * uvartype) list)

fun etype_vars e = type_vars

fun do_ho_matches gen_unify gen_unify_le e = let
  val homs = reset_homs()
in
  ho_match gen_unify gen_unify_le homs e
end

fun resolve_ho_matches () = let
  val unify    = gen_unify kind_unify kind_unify    conty_kind_unify rank_unify unsafe_bind " =" etype_vars
  val unify_le = gen_unify kind_unify kind_unify_le conty_kind_unify rank_unify unsafe_bind "<=" etype_vars
in
  (case (do_ho_matches unify unify_le empty_env)
    of (bindings, SOME ()) => ()
     | (_, NONE) => raise TCERR "unify" "unify failed"
  ) handle e as HOL_ERR _ => snd (!current_error_report) e
end

fun ho_gen_unify
              (kind_unify   :int -> prekind -> prekind -> ('a -> 'a * unit option))
              (kind_unify_le:int -> prekind -> prekind -> ('a -> 'a * unit option))
              (conty_kind_unify:int -> prekind -> prekind -> ('a -> 'a * unit option))
              (rank_unify   :int -> prerank -> prerank -> ('a -> 'a * unit option))
              bind cmp tyvars n c1 c2 t1 t2 e =
  let val unify1    = gen_unify kind_unify kind_unify    conty_kind_unify rank_unify bind " =" tyvars
      val unify1_le = gen_unify kind_unify kind_unify_le conty_kind_unify rank_unify bind "<=" tyvars
      val unify' = if cmp = "<=" then unify1_le else unify1
      val _ = begin_homs()
  in (unify' n c1 c2 t1 t2 >>
      do_ho_matches unify1 unify1_le) e
     before end_homs()
  end
  handle e as HOL_ERR _ => (end_homs(); raise e);

fun unify t1 t2 =
  let val t1' = deep_beta_eta_ty t1
      and t2' = deep_beta_eta_ty t2
      val _ = if not (is_debug()) then () else let
            val ty1s  = pretype_to_string t1
            val ty2s  = pretype_to_string t2
            val ty1s' = pretype_to_string t1'
            val ty2s' = pretype_to_string t2'
         in print (    "unify  " ^ ty1s'
                   ^ "\n   vs. " ^ ty2s' ^ "\n")
         end
  in
  case (gen_unify kind_unify kind_unify conty_kind_unify rank_unify unsafe_bind " =" etype_vars 0 [] [] t1' t2' empty_env)
   of (bindings, SOME ()) => ()
    | (_, NONE) => raise TCERR "unify" "unify failed"
                                    (* ("unify failed: " ^ pretype_to_string t1
                                    ^ "\n      versus: " ^ pretype_to_string t2) *)
  end;

fun ho_unify t1 t2 =
  let val t1' = deep_beta_eta_ty t1
      and t2' = deep_beta_eta_ty t2
      val _ = if not (is_debug()) then () else let
            val ty1s  = pretype_to_string t1
            val ty2s  = pretype_to_string t2
            val ty1s' = pretype_to_string t1'
            val ty2s' = pretype_to_string t2'
         in print (    "unify  " ^ ty1s'
                   ^ "\n   vs. " ^ ty2s' ^ "\n")
         end
  in
  case (ho_gen_unify kind_unify kind_unify_le conty_kind_unify rank_unify unsafe_bind " =" etype_vars 0 [] [] t1' t2' empty_env)
   of (bindings, SOME ()) => ()
    | (_, NONE) => raise TCERR "unify" "unify failed"
                                    (* ("unify failed: " ^ pretype_to_string t1
                                    ^ "\n      versus: " ^ pretype_to_string t2) *)
  end;

fun unify_le t1 t2 =
  let val t1' = deep_beta_eta_ty t1
      and t2' = deep_beta_eta_ty t2
      val _ = if not (is_debug()) then () else let
            val ty1s  = pretype_to_string t1
            val ty2s  = pretype_to_string t2
            val ty1s' = pretype_to_string t1'
            val ty2s' = pretype_to_string t2'
         in print (    "unify  " ^ ty1s'
                   ^ "\n   vs. " ^ ty2s' ^ "\n")
         end
  in
  case (gen_unify kind_unify kind_unify_le conty_kind_unify rank_unify unsafe_bind "<=" etype_vars 0 [] [] t1' t2' empty_env)
   of (bindings, SOME ()) => ()
    | (_, NONE) => raise TCERR "unify" "unify failed"
                                    (* ("unify failed: " ^ pretype_to_string t1
                                    ^ "\n      versus: " ^ pretype_to_string t2) *)
  end;

fun ho_unify_le t1 t2 =
  let val t1' = deep_beta_eta_ty t1
      and t2' = deep_beta_eta_ty t2
      val _ = if not (is_debug()) then () else let
            val ty1s  = pretype_to_string t1
            val ty2s  = pretype_to_string t2
            val ty1s' = pretype_to_string t1'
            val ty2s' = pretype_to_string t2'
         in print (    "unify  " ^ ty1s'
                   ^ "\n   vs. " ^ ty2s' ^ "\n")
         end
  in
  case (ho_gen_unify kind_unify kind_unify_le conty_kind_unify rank_unify unsafe_bind "<=" etype_vars 0 [] [] t1' t2' empty_env)
   of (bindings, SOME ()) => ()
    | (_, NONE) => raise TCERR "unify" "unify failed"
                                    (* ("unify failed: " ^ pretype_to_string t1
                                    ^ "\n      versus: " ^ pretype_to_string t2) *)
  end;

fun can_unify t1 t2 = let
  val ((rank_bindings,kind_bindings,type_bindings), result) =
        ho_gen_unify kind_unify kind_unify_le conty_kind_unify rank_unify unsafe_bind " =" etype_vars 0 [] [] t1 t2 empty_env
  val _ = app (fn (r, oldvalue) => r := oldvalue) rank_bindings
  val _ = app (fn (r, oldvalue) => r := oldvalue) kind_bindings
  val _ = app (fn (r, oldvalue) => r := oldvalue) type_bindings
in
  isSome result
end

fun can_unify_le t1 t2 = let
  val ((rank_bindings,kind_bindings,type_bindings), result) =
        ho_gen_unify kind_unify kind_unify_le conty_kind_unify rank_unify unsafe_bind "<=" etype_vars 0 [] [] t1 t2 empty_env
  val _ = app (fn (r, oldvalue) => r := oldvalue) rank_bindings
  val _ = app (fn (r, oldvalue) => r := oldvalue) kind_bindings
  val _ = app (fn (r, oldvalue) => r := oldvalue) type_bindings
in
  isSome result
end

fun print_safe_env n env =
  if not (is_debug()) then (env, SOME ()) else
  let 
    fun print1 (r, ty) =
      print (Int.toString(Portable.ref_to_int r) ^ " |-> "
               ^ pretype_to_string (THEU ty))
    fun printn (r_ty::r_tys) =
        let in
          print ("\n  " ^ spaces n);
          print1 r_ty;
          printn r_tys
        end
      | printn [] = print " "
  in
    print (spaces n^"[ ");
    if null env then ()
    else (print1 (hd env);
          printn (tl env));
    print "]\n";
    (env, SOME ())
  end

local
     fun (r ref_equiv (PT(value, locn))) (env as (renv,kenv,tenv)) =
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

      fun (r ref_occurs_in (PT(value, locn))) (env as (renv,kenv,tenv)) =
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
          | TyExis(tyv, ty) => (r ref_occurs_in tyv) env orelse
                               (r ref_occurs_in ty) env
          | TyAbst(tyv, ty) => (r ref_occurs_in tyv) env orelse
                               (r ref_occurs_in ty) env
          | TyKindConstr{Ty,...} => (r ref_occurs_in Ty) env
          | TyRankConstr{Ty,...} => (r ref_occurs_in Ty) env
          | _ => false

      fun kind_unify n k1 k2 (env as (renv,kenv,tenv)) =
        let val ((renv',kenv'), result) = Prekind.safe_unify n k1 k2 (renv,kenv)
        in ((renv',kenv',tenv), result)
        end

      fun kind_unify_le n k1 k2 (env as (renv,kenv,tenv)) =
        let val ((renv',kenv'), result) = Prekind.safe_unify_le n k1 k2 (renv,kenv)
        in ((renv',kenv',tenv), result)
        end

      fun conty_kind_unify n k1 k2 (env as (renv,kenv,tenv)) =
        let val ((renv',kenv'), result) = Prekind.safe_conty_unify n k1 k2 (renv,kenv)
        in ((renv',kenv',tenv), result)
        end

      fun rank_unify n r1 r2 (env as (renv,kenv,tenv)) =
        let val (renv', result) = Prerank.safe_unify n r1 r2 renv
        in ((renv',kenv,tenv), result)
        end

in
fun safe_bind n unify c1 c2 r value (env as (renv,kenv,tenv)) =
report "Binding safely = type" "= " n c1 c2 (PT(UVar r, locn.Loc_None)) value (fn (env as (renv,kenv,tenv)) =>
(print_safe_env n tenv;
  case Lib.assoc1 r tenv
   of SOME (_, v) => unify c1 c2 (THEU v) value env
    | NONE =>
        if (r ref_equiv value) env then ok env else
        if (r ref_occurs_in value) env orelse isSomeU (!r) then fail env
        else ((renv,kenv,(r, SOMEU (shift_context c2 c1 value))::tenv), SOME ())
)) env

val safe_unify0    = gen_unify kind_unify kind_unify    conty_kind_unify rank_unify safe_bind " =" deref_type_vars 0 [] []
val safe_unify_le0 = gen_unify kind_unify kind_unify_le conty_kind_unify rank_unify safe_bind "<=" deref_type_vars 0 [] []

val ho_safe_unify0    =
  ho_gen_unify kind_unify kind_unify_le conty_kind_unify rank_unify safe_bind " =" deref_type_vars 0 [] []
val ho_safe_unify_le0 =
  ho_gen_unify kind_unify kind_unify_le conty_kind_unify rank_unify safe_bind "<=" deref_type_vars 0 [] []

fun do_beta_first f t1 t2 = f (deep_beta_eta_ty t1) (deep_beta_eta_ty t2)

val safe_unify       = do_beta_first safe_unify0
val safe_unify_le    = do_beta_first safe_unify_le0
val ho_safe_unify    = do_beta_first ho_safe_unify0
val ho_safe_unify_le = do_beta_first ho_safe_unify_le0

end

(* Temporarily put in this test to check safe unification vs unsafe, for all normal unifications.
   Remove for deployment, but use for hard test of safe unification.
fun unify t1 t2 =
  let val (safe_bindings, safe_res) = safe_unify t1 t2 ([],[],[])
      val t1' = deep_beta_eta_ty t1
      and t2' = deep_beta_eta_ty t2
      val _ = if not (is_debug()) then () else let
            val ty1s  = pretype_to_string t1
            val ty2s  = pretype_to_string t2
            val ty1s' = pretype_to_string t1'
            val ty2s' = pretype_to_string t2'
         in print (    "unify  " ^ ty1s'
                   ^ "\n   vs. " ^ ty2s' ^ "\n")
         end
  in
  case (gen_unify kind_unify kind_unify conty_kind_unify rank_unify unsafe_bind " =" etype_vars 0 [] [] t1' t2' empty_env)
   of (bindings, SOME ()) =>
        let in case safe_res
                of SOME () => ()
                 | NONE => (print ("\nsafe unify wrongly failed on:\n" ^ pretype_to_string t1
                                   ^ "\nversus:\n" ^ pretype_to_string t2 ^ "\n");
                                   raise TCERR "safe unify" "safe unify failed")
        end
    | (_, NONE) => case safe_res
                    of SOME () => (print ("\nsafe unify wrongly succeeded on:\n" ^ pretype_to_string t1
                                          ^ "\nversus:\n" ^ pretype_to_string t2 ^ "\n");
                                   raise TCERR "safe unify" "safe unify failed")
                     | NONE =>
                   raise TCERR "unify" "unify failed"
  end;
*)

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
  val ((rkenv1,kdenv1), res1) = m1 (rkenv,kdenv)
in
  case res1 of
    NONE => ((rkenv1,kdenv1,tyenv), NONE)
  | SOME res => f res (rkenv1,kdenv1,tyenv)
end

fun (m1 >>= f) (env as (rkenv,kdenv,tyenv)) = let
  val (rkenv1, res1) = m1 rkenv
in
  case res1 of
    NONE => ((rkenv1,kdenv,tyenv), NONE)
  | SOME res => f res (rkenv1,kdenv,tyenv)
end

local
(*
  fun push_rv (rk::rkenv,kdenv) =
      let val rk' = Prerank.new_uvar()
      in Prerank.unify_le rk' (* :<=: *) rk;
         ((rk'::rk::rkenv,kdenv), SOME ())
      end
    | push_rv (rkenv,kdenv) =
      ((Prerank.new_uvar()::rkenv,kdenv), SOME ())
  fun pop_rv (_::rkenv,kdenv,tyenv) =
      ((rkenv,kdenv,tyenv), SOME ())
    | pop_rv (rkenv,kdenv,tyenv) =
      ((rkenv,kdenv,tyenv), NONE)
*)
  val rename_kv = Prekind.rename_kv
  fun rename_kv_new avds kd (env as (rkenv,kdenv)) =
    let val ((_,kdenv'), result) = rename_kv avds kd ([],kdenv)
    in ((rkenv,kdenv'), result)
    end
  val rename_rv = Prerank.rename_rv
  fun replace kdavds (s,kd) (env as (rkenv,kdenv,tyenv)) =
      case Lib.assoc1 s tyenv of
        NONE => let
          val ((rkenv',kdenv'), skd') = rename_kv_new kdavds kd (rkenv,kdenv)
          val kd' = case skd' of SOME kd' => kd' | NONE => kd
          val r = new_uvar kd'
        in
          ((rkenv',kdenv',(s, r)::tyenv), SOME r)
        end
      | SOME (_, r) => (env, SOME r)
  fun add_bvar (v as PT(Vartype (s,kd), l)) kdavds avds =
          rename_kv kdavds kd >>- (fn kd' =>
          let val v' = PT(Vartype (s,kd'), l)
          in return (s::avds, v')
          end)
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
    Vartype (v as (s,kd)) =>
       (* may create a new rank uvar as a local value for rho within the kind of v,
          which will be matched to be equal to the ranks of all bindings of the type var *)
       if mem s avds then (rename_kv kdavds kd >>- (fn kd' =>
                           return (PT(Vartype(s,kd'), locn))))
       else replace kdavds (s,kd)
(*
       rename_kv kdavds kd >>- (fn kd' =>
       if mem s avds then return (PT(Vartype(s,kd'), locn)) else replace (s,kd'))
*)
(*
       case Lib.assoc1 s benv
         of SOME _ => return (PT(Vartype(s,kd'), locn))
          | NONE   => replace (s,kd')))
*)
  | Contype {Thy,Tyop,Kind} =>
       if Prekind.is_type_kind Kind
       then (* don't rename zero ranks; this constant type need not promote (save on uvars!). *)
         return ty
       else
       (* rename_kv kdavds Kind *) (* rename_kv to replace zero Ranks w/ std uvar. *)
       rename_kv_new kdavds Kind (* rename_kv_new to replace zero Ranks w/ new uvar. *)
          >>- (fn Kind' =>
       return (PT(Contype {Thy=Thy,Tyop=Tyop,Kind=Kind'}, locn)))
  | TyApp (ty1, ty2) =>
      rename_tv kdavds avds ty1 >- (fn ty1' =>
      rename_tv kdavds avds ty2 >- (fn ty2' =>
      return (PT(TyApp(ty1', ty2'), locn))))
  | TyUniv (ty1, ty2) =>
      add_bvar ty1 kdavds avds >- (fn (avds',ty1') =>
      rename_tv kdavds avds' ty2 >- (fn ty2' =>
      return (PT(TyUniv(ty1', ty2'), locn))))
  | TyExis (ty1, ty2) =>
      add_bvar ty1 kdavds avds >- (fn (avds',ty1') =>
      rename_tv kdavds avds' ty2 >- (fn ty2' =>
      return (PT(TyExis(ty1', ty2'), locn))))
  | TyAbst (ty1, ty2) =>
      add_bvar ty1 kdavds avds >- (fn (avds',ty1') =>
      rename_tv kdavds avds' ty2 >- (fn ty2' =>
      return (PT(TyAbst(ty1', ty2'), locn))))
  | TyKindConstr {Ty, Kind} =>
      rename_kv kdavds Kind >>- (fn Kind' =>
      rename_tv kdavds avds Ty >- (fn Ty' =>
      return (PT(TyKindConstr {Ty=Ty', Kind=Kind'}, locn))))
  | TyRankConstr {Ty, Rank} =>
      rename_rv Rank >>= (fn Rank' =>
      rename_tv kdavds avds Ty >- (fn Ty' =>
      return (PT(TyRankConstr {Ty=Ty', Rank=Rank'}, locn))))
  | UVar (r as ref (SOMEU ty)) =>
      rename_tv kdavds avds ty >- (fn ty' =>
      (r := SOMEU ty'; return (PT(UVar r, locn))))
  | UVar (r as ref (NONEU kd)) =>
      rename_kv kdavds kd >>- (fn kd' =>
      (r := NONEU kd'; return (PT(UVar r, locn))))
(* | _ (* UVar (ref _) *) => return ty *)

fun rename_typevars kdavds avds ty = valOf (#2 (rename_tv kdavds avds ty ([],[],[])))
end

fun fromType t =
  if Type.is_var_type t then let
      val (str, kd) = Type.dest_var_type t
    in
      PT(Vartype (str, Prekind.fromKind kd), locn.Loc_None)
    end
  else if Type.is_con_type t then let
      val {Thy, Tyop, Kind} = dest_thy_con_type t
    in
      PT(Contype {Kind=Prekind.fromKind Kind,
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
  else if Type.is_exist_type t then let
      val (ty1, ty2) = Type.dest_exist_type t
    in
      PT(TyExis(fromType ty1, fromType ty2), locn.Loc_None)
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
  | UVar(r as ref (NONEU kd)) => (r := NONEU (Prekind.remove_made_links kd); PT(UVar r, locn))
  | Vartype(s,kd) => PT(Vartype(s, Prekind.remove_made_links kd), locn)
  | Contype {Thy, Tyop, Kind} =>
      PT(Contype {Kind=Prekind.remove_made_links Kind, Thy=Thy, Tyop=Tyop}, locn)
  | TyApp(ty1, ty2) => PT(TyApp (remove_made_links ty1, remove_made_links ty2), locn)
  | TyUniv(tyv, ty) => PT(TyUniv(remove_made_links tyv, remove_made_links ty), locn)
  | TyExis(tyv, ty) => PT(TyExis(remove_made_links tyv, remove_made_links ty), locn)
  | TyAbst(tyv, ty) => PT(TyAbst(remove_made_links tyv, remove_made_links ty), locn)
  | TyKindConstr {Ty, Kind} =>
      PT(TyKindConstr {Ty=remove_made_links Ty, Kind=Prekind.remove_made_links Kind}, locn)
  | TyRankConstr {Ty, Rank} =>
      PT(TyRankConstr {Ty=remove_made_links Ty, Rank=Prerank.remove_made_links Rank}, locn)

val tyvariant = Lexis.gen_variant Lexis.tyvar_vary

(* needs changing *)
fun generate_new_name r kd (kenv, used_so_far) =
  let val result = tyvariant used_so_far "'a"
      val _ = r := SOMEU (PT(Vartype (result,kd), locn.Loc_None))
  in
    ((kenv, result::used_so_far), SOME ())
  end

fun kind_replace_null_links kd (kenv,tenv) =
    let val (((), kenv'), result) = Prekind.replace_null_links kd ((),kenv)
    in ((kenv',tenv), result)
    end

(*
fun var_kind_replace_null_links kd (kenv,tenv) =
    let val (((), kenv'), result) = Prekind.var_replace_null_links kd ((),kenv)
    in ((kenv',tenv), result)
    end
*)

fun rank_replace_null_links rk (kenv,tenv) =
    let val ((), result) = Prerank.replace_null_links rk ()
    in ((kenv,tenv), result)
    end

(* eta-expansion (see "env" after end below) *is* necessary *)
fun replace_null_links (PT(ty,_)) env = let
in
  case ty of
    UVar (r as ref (NONEU kd)) => kind_replace_null_links kd >>
                                  generate_new_name r kd
  | UVar (ref (SOMEU ty)) => replace_null_links ty
  | TyApp (ty1,ty2) => replace_null_links ty1 >> replace_null_links ty2 >> ok
  | TyUniv (tyv, ty) => replace_null_links tyv >> replace_null_links ty >> ok
  | TyExis (tyv, ty) => replace_null_links tyv >> replace_null_links ty >> ok
  | TyAbst (tyv, ty) => replace_null_links tyv >> replace_null_links ty >> ok
  | TyKindConstr {Ty,Kind} => replace_null_links Ty >> kind_replace_null_links Kind >> ok
  | TyRankConstr {Ty,Rank} => replace_null_links Ty >> rank_replace_null_links Rank >> ok
  | Vartype (s,kd) => kind_replace_null_links kd
  | Contype {Thy,Tyop,Kind} => kind_replace_null_links Kind
end env

fun clean (pty as PT(ty, locn)) =
(
  case ty of
    Vartype (s,kd) => Type.mk_var_type (s, Prekind.toKind kd)
  | Contype {Thy,Tyop,Kind} => Type.mk_thy_con_type {Thy=Thy, Tyop=Tyop,
                                    Kind=Prekind.toKind Kind}
  | TyApp(ty1,ty2)  => (Type.mk_app_type  (clean ty1, clean ty2)
                          handle Feedback.HOL_ERR e =>
                            ((*print ("Applying " ^ type_to_string (clean ty1)
                                    ^ " to " ^ type_to_string (clean ty2) ^ "\n");*)
                             raise Feedback.mk_HOL_ERR "Pretype" "clean" (#message e)))
  | TyUniv (tyv,ty) => Type.mk_univ_type (clean tyv, clean ty)
  | TyExis (tyv,ty) => Type.mk_exist_type (clean tyv, clean ty)
  | TyAbst (tyv,ty) => Type.mk_abs_type  (clean tyv, clean ty)
  | TyKindConstr {Ty,Kind} => clean Ty
  | TyRankConstr {Ty,Rank} => clean Ty
  | _ => raise Fail "Don't expect to see links remaining at this stage of type inference"
) handle e => Raise (wrap_exn "Pretype.clean" (pretype_to_string pty) e)

fun toType ty =
  let val ty = if do_beta_conv_types()
                      then deep_beta_eta_ty ty
                      else ty
      val _ = replace_null_links ty (kindvars ty, tyvars ty)
  in
    clean (remove_made_links ty)
  end
  handle e => raise (wrap_exn "Pretype" "toType" e)

(*
val fun_tyc0 = Contype{Tyop = "fun", Thy = "min",
                       Kind = Prekind.mk_arity 2}
*)

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
  fun throw_non_unify (e as Feedback.HOL_ERR{origin_structure,origin_function,message}) =
         if mem origin_structure ["Prerank","Prekind"] andalso
            mem origin_function ["unify","unify_le"] then ()
         else raise e
    | throw_non_unify e = raise e
in
fun KC printers = let
  val prk = Rank.rank_to_string
  val (pty, pkd) =
      case printers
       of SOME (y,z) =>
          let val kdprint = z
              fun typrint ty =
                  if Type.is_con_type ty
                  then (y ty ^ " : " ^ z (Type.kind_of ty))
                  else y ty
          in
            (typrint, kdprint)
          end
        | NONE => (default_typrinter, default_kdprinter)
  val checkrank = Prekind.checkrank (case printers of SOME (x,y) => SOME y | NONE => NONE)
  val prekind_to_string = Prekind.prekind_to_string
  fun check(PT(TyApp(opr,arg),locn)) =
      (check opr;
       check arg;
       if not (is_debug()) then () else
        (print ("\n(Checking type application:\n" ^ pretype_to_string opr ^ "\napplied to\n"
                 ^ pretype_to_string arg ^ "\n"));
       ((**)if Prekind.is_arrow_kind (pkind_of opr) (* optimize; cut out unnecessary unifications *)
        then Prekind.unify_le (pkind_of arg) (* :<=: *) (fst (Prekind.dom_rng (pkind_of opr)))
        else(**) Prekind.unify_le (pkind_of arg ==> Prekind.all_new_uvar())
                                                 (* Prekind.new_uvar(prank_of_type opr) *)
                              (* :<=: *) (pkind_of opr);
       if not (is_debug()) then () else
        (print ("\n)Checked type application:\n" ^ pretype_to_string opr ^ "\napplied to\n"
                 ^ pretype_to_string arg ^ "\n")) )
       handle (e as Feedback.HOL_ERR{origin_structure,origin_function,message})
       => let val _ = throw_non_unify e
              val show_ranks = Feedback.get_tracefn "ranks"
              val tmp = show_ranks()
              val _   = Feedback.set_trace "ranks" 1
              val opr' = toType opr
                handle e => (Feedback.set_trace "ranks" tmp; raise e)
              val arg' = toType arg
                handle e => (Feedback.set_trace "ranks" tmp; raise e)
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
            Feedback.set_trace "ranks" tmp;
            kcheck_say message;
            last_kcerror := SOME (TyAppFail(opr',arg'), Locn arg);
            raise ERRloc"kindcheck" (Locn opr (* arbitrary *)) "failed"
          end)
    | check (PT(Vartype(Name, Kind), Locn)) =
       (if not (is_debug()) then () else
          print ("\nChecking kind of type variable \"" ^ Name ^"\":\n" ^ prekind_to_string Kind ^ "\n");
        checkrank Kind
       )
    | check (PT(Contype{Thy, Tyop, Kind}, Locn)) =
       (if not (is_debug()) then () else
          print ("\nChecking kind of type constant \"" ^ Tyop ^"\":\n" ^ prekind_to_string Kind ^ "\n");
        checkrank Kind
       )
    | check (PT(TyUniv(Bvar, Body), locn)) =
       (check Bvar; check Body;
        if not (is_debug()) then () else
          print ("\nChecking kind of body of universal type is type kind:\n" ^ pretype_to_string Body ^ "\n");
        Prekind.unify (pkind_of Body) (Prekind.typ (Prerank.new_uvar()))
       handle (e as Feedback.HOL_ERR{origin_structure,origin_function,message})
       => let val _ = throw_non_unify e
              val show_ranks = Feedback.get_tracefn "ranks"
              val tmp = show_ranks()
              val _   = Feedback.set_trace "ranks" 1
              val real_type = toType Body
                handle e => (Feedback.set_trace "ranks" tmp; raise e)
              val message =
                  String.concat
                      [
                       "\nKind inference failure: the type\n\n",
                       pty real_type,
                       "\n\n"^locn.toString (Locn Body)^"\n\n",
                       if (is_atom Body) then ""
                       else ("which has kind\n\n" ^
                             pkd(Type.kind_of real_type) ^ "\n\n"),

                       "can not be constrained to be of kind ty\n\n",

                       "kind unification failure message: ", message, "\n"]
          in
            Feedback.set_trace "ranks" tmp;
            kcheck_say message;
            last_kcerror := SOME (TyUnivFail(real_type), Locn Body);
            raise ERRloc "kindcheck" locn "failed"
          end)
    | check (PT(TyExis(Bvar, Body), locn)) =
       (check Bvar; check Body;
        if not (is_debug()) then () else
          print ("\nChecking kind of body of existential type is type kind:\n" ^ pretype_to_string Body ^ "\n");
        Prekind.unify (pkind_of Body) (Prekind.typ (Prerank.new_uvar()))
       handle (e as Feedback.HOL_ERR{origin_structure,origin_function,message})
       => let val _ = throw_non_unify e
              val show_ranks = Feedback.get_tracefn "ranks"
              val tmp = show_ranks()
              val _   = Feedback.set_trace "ranks" 1
              val real_type = toType Body
                handle e => (Feedback.set_trace "ranks" tmp; raise e)
              val message =
                  String.concat
                      [
                       "\nKind inference failure: the type\n\n",
                       pty real_type,
                       "\n\n"^locn.toString (Locn Body)^"\n\n",
                       if (is_atom Body) then ""
                       else ("which has kind\n\n" ^
                             pkd(Type.kind_of real_type) ^ "\n\n"),

                       "can not be constrained to be of kind ty\n\n",

                       "kind unification failure message: ", message, "\n"]
          in
            Feedback.set_trace "ranks" tmp;
            kcheck_say message;
            last_kcerror := SOME (TyExisFail(real_type), Locn Body);
            raise ERRloc "kindcheck" locn "failed"
          end)
    | check (PT(TyAbst(Bvar, Body), Locn)) = (check Bvar; check Body)
    | check (PT(TyKindConstr{Ty,Kind},locn)) =
       (check Ty; checkrank Kind;
       if not (is_debug()) then () else
         print ("\nChecking kind constraint of type:\n" ^ pretype_to_string Ty ^ "\ncompared to\n"
                 ^ prekind_to_string Kind ^ "\n");
        Prekind.unify (pkind_of Ty) Kind
       handle (e as Feedback.HOL_ERR{origin_structure,origin_function,message})
       => let val _ = throw_non_unify e
              val show_ranks = Feedback.get_tracefn "ranks"
              val tmp = show_ranks()
              val _   = Feedback.set_trace "ranks" 1
              val real_type = toType Ty
                handle e => (Feedback.set_trace "ranks" tmp; raise e)
              val Prekind.PK(_,kd_locn) = Kind
              val real_kind = Prekind.toKind Kind
                handle e => (Feedback.set_trace "ranks" tmp; raise e)
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
            Feedback.set_trace "ranks" tmp;
            kcheck_say message;
            last_kcerror := SOME (TyKindConstrFail(real_type, real_kind), kd_locn);
            raise ERRloc "kindcheck" locn "failed"
          end)
    | check (PT(TyRankConstr{Ty,Rank},locn)) =
       (check Ty;
        if not (is_debug()) then () else
          print ("\nChecking rank constraint of type:\n" ^ pretype_to_string Ty ^ "\ncompared to\n"
                  ^ Prerank.prerank_to_string Rank ^ "\n");
        Prerank.unify (prank_of_type Ty) Rank
       handle (e as Feedback.HOL_ERR{origin_structure,origin_function,message})
       => let val _ = throw_non_unify e
              val show_ranks = Feedback.get_tracefn "ranks"
              val tmp = show_ranks()
              val _   = Feedback.set_trace "ranks" 1
              val real_type = toType Ty
                handle e => (Feedback.set_trace "ranks" tmp; raise e)
              val real_rank = Prerank.toRank Rank
                handle e => (Feedback.set_trace "ranks" tmp; raise e)
              val message =
                  String.concat
                      [
                       "\nRank inference failure: the type\n\n",
                       pty real_type,
                       "\n\n"^locn.toString (Locn Ty)^"\n\n",
                       if (is_atom Ty) then ""
                       else ("which has rank " ^
                             prk(Type.rank_of_type real_type) ^ "\n\n"),

                       "can not be constrained to be ",
                       if origin_function="unify" then "of" else "<=",
                       " rank ",
                       prk real_rank, "\n\n",

                       "rank unification failure message: ", message, "\n"]
          in
            Feedback.set_trace "ranks" tmp;
            kcheck_say message;
            last_kcerror := SOME ( (if origin_function="unify" then TyRankConstrFail else TyRankLEConstrFail)
                                   (real_type, real_rank), locn);
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
           val args = map (fn bvar => new_uvar(pkind_of bvar)) bvars
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
        (* val _ = KC NONE pty *) (* unnecessary; the new uvars have copies of the right kinds *)
    in (*reset_rank_uvars pty;*)
       pty
    end
(*
fun test_reconcile_univ_types pat targ =
    let val pty = reconcile (deep_beta_eta_ty pat) (deep_beta_eta_ty targ)
        val zty = all_new_uvar()
        val (bindings, result) =
          gen_unify kind_unify kind_unify conty_kind_unify rank_unify unsafe_bind " =" etype_vars 0 [] [] pty zty empty_env
        (* bindings = (rank_bindings,kind_bindings,type_bindings) *)
    in (bindings, pty)
    end
fun unwind_bindings (rank_bindings,kind_bindings,type_bindings) =
         (app (fn (r, oldvalue) => r := oldvalue) rank_bindings;
          app (fn (r, oldvalue) => r := oldvalue) kind_bindings;
          app (fn (r, oldvalue) => r := oldvalue) type_bindings; ())
*)
end

fun remove_ty_aq t =
  if parse_type.is_ty_antiq t then parse_type.dest_ty_antiq t
  else raise mk_HOL_ERR "Parse" "type parser" "antiquotation is not of a type"

(* "qtyop" refers to "qualified" type operator, i.e., qualified by theory name. *)

fun mk_conty{Thy,Tyop,Kind,Locn} =
  PT(Contype {Thy=Thy, Tyop=Tyop, Kind=Kind}, Locn)

fun do_qtyop {Thy,Tyop,Locn,Args} =
  List.foldl (fn (arg,acc) => PT(TyApp(acc,arg),Locn))
             (mk_conty{Thy=Thy,Tyop=Tyop,Kind=Prekind.mk_arity(length Args),Locn=Locn})
             Args

fun tyop_to_qtyop ((tyop,locn), args) =
  case Type.decls tyop of
    [] => raise mk_HOL_ERRloc "Parse" "type parser" locn
                              (tyop^" not a known type operator")
  | {Thy,Tyop} :: _ =>
      let val prim_kd = prim_kind_of{Thy=Thy, Tyop=Tyop}
          val pre_kd = case Prekind.rename_kv [] (Prekind.fromKind prim_kd) ([],[])
                         of (_, SOME pre_kd) => pre_kd
                          | _ => raise ERR "tyop_to_qtyop" "impossible"
          val c = mk_conty{Thy=Thy,Tyop=Tyop,Kind=pre_kd,Locn=locn}
      in list_mk_app_type(c, args)
      end
      (* do_qtyop {Thy = Thy, Tyop = Tyop, Locn = locn, Args = args} *)

fun do_kindcast {Ty,Kind,Locn} =
  PT(TyKindConstr {Ty=Ty,Kind=Kind}, Locn)

fun do_rankcast {Ty,Rank,Locn} =
  PT(TyRankConstr {Ty=Ty,Rank=Rank}, Locn)

fun mk_basevarty((s,kd),locn) = PT(Vartype(s,kd), locn)

val termantiq_constructors =
    {vartype = mk_basevarty, qtyop = do_qtyop,
     tyop = tyop_to_qtyop,
     antiq = fn x => fromType (remove_ty_aq x),
     kindcast = do_kindcast, rankcast = do_rankcast,
     tycon = mk_conty, tyapp = mk_app_type,
     tyuniv = mk_univ_type, tyexist = mk_exist_type, tyabs = mk_abs_type}

val typantiq_constructors =
    {vartype = mk_basevarty, qtyop = do_qtyop,
     tyop = tyop_to_qtyop,
     antiq = fromType,
     kindcast = do_kindcast, rankcast = do_rankcast,
     tycon = mk_conty, tyapp = mk_app_type,
     tyuniv = mk_univ_type, tyexist = mk_exist_type, tyabs = mk_abs_type}

end;
