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

val debug = ref 0
val _ = Feedback.register_trace("debug_pretype", debug, 1)
fun is_debug() = (!debug) > 0;

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
    | UVar of uvartype ref
 and uvartype
    = SOMEU of pretype
    | NONEU of prekind * prerank
 and pretype = PT of pretype0 locn.located

fun isSomeU (SOMEU _) = true
  | isSomeU (NONEU _) = false

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
  | eq_env0 e1 e2 (UVar (r  as ref (NONEU(kd, rk ))))
                  (UVar (r' as ref (NONEU(kd',rk'))))                  = r=r'
  | eq_env0 e1 e2 (UVar (ref (SOMEU ty)))    (UVar (ref (SOMEU ty')))  = eq_env e1 e2 ty ty'
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

fun dest_var_type(PT(Vartype v,loc)) = v
  | dest_var_type(PT(UVar(ref(SOMEU ty)),loc)) = dest_var_type ty
  | dest_var_type _ = raise TCERR "dest_var_type" "not a type variable";

fun the_var_type(ty as PT(Vartype v,loc)) = ty
  | the_var_type(PT(TyKindConstr{Ty,Kind},loc)) = the_var_type Ty
  | the_var_type(PT(TyRankConstr{Ty,Rank},loc)) = the_var_type Ty
  | the_var_type(PT(UVar(ref(SOMEU ty)),loc))   = the_var_type ty
  | the_var_type(ty as PT(UVar(ref(NONEU _)),loc)) = ty
  | the_var_type _ = raise TCERR "the_var_type" "not a type variable";

fun mk_app_type(ty1 as PT(_,loc1), ty2 as PT(_,loc2)) =
    PT(TyApp(ty1,ty2), locn.between loc1 loc2)

fun dest_app_type(PT(UVar(ref(SOMEU ty)),loc)) = dest_app_type ty
  | dest_app_type(ty as PT(TyApp(ty1,ty2),loc)) = (ty1,ty2)
  | dest_app_type _ = raise TCERR "dest_app_type" "not a type application";

fun mk_univ_type(ty1 as PT(_,loc1), ty2 as PT(_,loc2)) =
    PT(TyUniv(ty1,ty2), locn.between loc1 loc2)

fun dest_univ_type(PT(UVar(ref(SOMEU ty)),loc)) = dest_univ_type ty
  | dest_univ_type(ty as PT(TyUniv(ty1,ty2),loc)) = (ty1,ty2)
  | dest_univ_type _ = raise TCERR "dest_univ_type" "not a universal type";

fun mk_abs_type(ty1 as PT(_,loc1), ty2 as PT(_,loc2)) =
    PT(TyAbst(ty1,ty2), locn.between loc1 loc2)

fun dest_abs_type(PT(UVar(ref(SOMEU ty)),loc)) = dest_abs_type ty
  | dest_abs_type(ty as PT(TyAbst(ty1,ty2),loc)) = (ty1,ty2)
  | dest_abs_type _ = raise TCERR "dest_abs_type" "not a type abstraction";

fun the_abs_type(PT(UVar(ref(SOMEU ty))  ,loc)) = the_abs_type ty
  | the_abs_type(PT(TyKindConstr{Ty,Kind},loc)) = the_abs_type Ty
  | the_abs_type(PT(TyRankConstr{Ty,Rank},loc)) = the_abs_type Ty
  | the_abs_type(ty as PT(TyAbst(ty1,ty2),loc)) = ty
  | the_abs_type _ = raise TCERR "the_abs_type" "not a type abstraction";

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

local fun TV (v as PT(Vartype _,_)) B A k = if mem v B then k A
                                            else k (Lib.insert v A)
        | TV (PT(Contype _,_)) B A k      = k A
        | TV (PT(TyApp(opr, ty),_)) B A k = TV opr B A (fn q => TV ty B q k)
        | TV (PT(TyUniv(v,ty),_)) B A k   = TV ty (Lib.insert v B) A k
        | TV (PT(TyAbst(v,ty),_)) B A k   = TV ty (Lib.insert v B) A k
        | TV (PT(TyKindConstr{Ty,Kind},_)) B A k = TV Ty B A k
        | TV (PT(TyRankConstr{Ty,Rank},_)) B A k = TV Ty B A k
        | TV (PT(UVar(ref(NONEU _ )),_)) B A k = k A
        | TV (PT(UVar(ref(SOMEU ty)),_)) B A k = TV ty B A k
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

fun gen_variant caller =
  let fun var_name (PT(Vartype(Name,_,_),_)) = Name
        | var_name _ = raise ERR caller "not a variable"
      fun vary vlist (PT(Vartype(Name,Kind,Rank),locn)) =
          let val L = map var_name vlist
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

val variant_type       = gen_variant "variant_type";


val op ==> = Prekind.==>
fun pkind_of0 (Vartype(s,kd,rk)) = kd
  | pkind_of0 (Contype{Kind, ...}) = Kind
  | pkind_of0 (TyApp(opr,arg)) = Prekind.chase (pkind_of opr)
  | pkind_of0 (TyUniv _) = Prekind.typ
  | pkind_of0 (TyAbst(Bvar,Body)) = pkind_of Bvar ==> pkind_of Body
  | pkind_of0 (TyKindConstr{Ty,Kind}) = Kind
  | pkind_of0 (TyRankConstr{Ty,Rank}) = pkind_of Ty
  | pkind_of0 (UVar (r as ref (NONEU(kd,rk)))) = kd
  | pkind_of0 (UVar (r as ref (SOMEU ty))) = pkind_of ty
and pkind_of (pty as PT(ty,locn)) = pkind_of0 ty


local
val zero = Prerank.Zerorank
val inc  = Prerank.Sucrank
val max  = Prerank.Maxrank
in
fun prank_of0 (Vartype(s,kd,rk)) = rk
  | prank_of0 (Contype{Rank, ...}) = Rank
  | prank_of0 (TyApp(opr,arg))     =     max(prank_of opr,  prank_of arg)
  | prank_of0 (TyUniv(Bvar,Body))  = inc(max(prank_of Bvar, prank_of Body))
  | prank_of0 (TyAbst(Bvar,Body))  =     max(prank_of Bvar, prank_of Body)
  | prank_of0 (TyKindConstr{Ty,Kind}) = prank_of Ty
  | prank_of0 (TyRankConstr{Ty,Rank}) = Rank
  | prank_of0 (UVar (r as ref (NONEU(_,rk)))) = rk
  | prank_of0 (UVar (r as ref (SOMEU ty))) = prank_of ty
and prank_of (PT(ty,locn)) = prank_of0 ty
end;


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
      let open Prekind Prerank
      in   (if prekind_compare(kd,typ) = EQUAL
            then "" else "::" ^ prekind_to_string kd)
         ^ (if prerank_compare(rk,Zerorank) = EQUAL
            then "" else ":<=" ^ prerank_to_string rk)
      end

fun pretype_to_string (ty as PT(ty0,locn)) =
  case ty0 of
    UVar(ref (SOMEU ty')) => pretype_to_string ty'
  | UVar(ref (NONEU(kd,rk))) => "<uvar>" ^ kind_rank_to_string(kd,rk)
  | Vartype(s,kd,rk) => s ^ kind_rank_to_string(kd,rk)
  | Contype {Thy, Tyop, Kind, Rank} => Tyop (* ^ kind_rank_to_string(Kind,Rank) *)
  | TyApp(PT(TyApp(PT(Contype{Tyop="fun",...},_), ty1),_), ty2)
                    => "(" ^ pretype_to_string ty1 ^ " -> " ^ pretype_to_string ty2 ^ ")"
  | TyApp(ty1, ty2) => "(" ^ pretype_to_string ty2 ^ " " ^ pretype_to_string ty1 ^ ")"
  | TyUniv(tyv, ty) => "!"  ^ pretype_to_string tyv ^ ". " ^ pretype_to_string ty
  | TyAbst(tyv, ty) => "\\" ^ pretype_to_string tyv ^ ". " ^ pretype_to_string ty
  | TyKindConstr {Ty, Kind} => pretype_to_string Ty ^ " : " ^ kind_to_string(Prekind.toKind Kind)
  | TyRankConstr {Ty, Rank} => pretype_to_string Ty ^ " :<= " ^ Int.toString(Prerank.toRank Rank)

fun pretypes_to_string tys = "[" ^ pretypes_to_string0 tys ^ "]"
and pretypes_to_string0 [ty] = pretype_to_string ty
  | pretypes_to_string0 (ty::tys) = pretype_to_string ty ^ ","
                                     ^ pretypes_to_string0 tys
  | pretypes_to_string0 [] = ""


(*---------------------------------------------------------------------------*
 *    Replace arbitrary subpretypes in a pretype. Renaming.                  *
 *---------------------------------------------------------------------------*)

val emptysubst:(pretype,pretype)Binarymap.dict = Binarymap.mkDict compare
local
  open Binarymap
  fun addb [] A = A
    | addb ({redex,residue}::t) (A,b) =
      addb t (if true (* Prerank.leq (prank_of residue) (prank_of redex) *)
                      (* ignore rank for now; should we unify these ranks? *)
              then (insert(A,redex,residue),
                    is_var_type redex andalso b)
              else raise ERR "type_subst" ("redex has lower rank than residue:\n" ^
                           "redex   : " ^ pretype_to_string redex ^ "\n" ^
                           "residue : " ^ pretype_to_string residue))
  fun variant_ptype fvs v = if is_var_type v then variant_type fvs v else v
  (* fun unloc_of (PT(ty,loc)) = ty *)
in
fun type_subst [] = I
  | type_subst theta =
    let val frees = type_vars_subst theta
        val (fmap,b) = addb theta (emptysubst, true)
        fun vsubs0 fmap (v as Vartype _) =
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
                   val fvs = Lib.op_set_diff eq (type_vars Body) [Bvar1]
                   val Bvar' = variant_ptype (Lib.op_union eq frees fvs) Bvar1
               in if eq Bvar1 Bvar' then TyUniv(Bvar, vsubs fmap Body)
                  else let val fmap' = insert(fmap,Bvar1,Bvar')
                       in TyUniv(vsubs fmap' Bvar, vsubs fmap' Body)
                       end
               end
          | vsubs0 fmap (TyAbst(Bvar,Body)) =
               let val Bvar1 = the_var_type Bvar
(*
                   val _ = if not(is_debug()) then () else
                           print ("vsubs: Bvar1 = " ^
                                  pretype_to_string Bvar1 ^ "\n")
                   val _ = if not(is_debug()) then () else
                           print ("vsubs: frees = " ^
                                  pretypes_to_string frees ^ "\n")
*)
                   val fvs = Lib.op_set_diff eq (type_vars Body) [Bvar1]
(*
                   val _ = if not(is_debug()) then () else
                           print ("vsubs: fvs   = " ^
                                  pretypes_to_string fvs ^ "\n")
*)
                   val Bvar' = variant_ptype (Lib.op_union eq frees fvs) Bvar1
(*
                   val _ = if not(is_debug()) then () else
                           print ("vsubs: Bvar' = " ^
                                  pretype_to_string Bvar' ^ "\n")
*)
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

local
val BERR = ERR "beta_conv_ty" "not a type beta redex"
in
fun beta_conv_ty (PT(TyApp(M, N), _))
       = let val _ = if not (is_debug()) then () else
                     print ("beta_conv_ty: M = " ^ pretype_to_string M ^ "\n"
                          ^ "              N = " ^ pretype_to_string N ^ "\n")
             val (Bnd,Body) = dest_abs_type (the_abs_type M)
                              handle HOL_ERR _ => raise BERR
             val _ = if not (is_debug()) then () else
                     print ("beta_conv_ty: Bnd  = " ^ pretype_to_string Bnd  ^ "\n"
                          ^ "              Body = " ^ pretype_to_string Body ^ "\n")
             val  Bvar      = the_var_type Bnd
                              handle HOL_ERR _ => raise BERR
             val _ = if not (is_debug()) then () else
                     print ("beta_conv_ty: Bvar = " ^ pretype_to_string Bvar ^ "\n")
             val _ = Prekind.unify (pkind_of N) (pkind_of Bvar);
             val _ = Prerank.unify (prank_of N) (prank_of Bvar);
             val _ = if not (is_debug()) then () else
                     print ("beta_conv_ty: kind and rank unified; about to subst\n");
             val Res = type_subst [Bvar |-> N] Body
                       handle e => Raise e
             val _ = if not (is_debug()) then () else
                     print ("beta_conv_ty: Res  = " ^ pretype_to_string Res ^ "\n")
         in Res
         end
  | beta_conv_ty _ = raise BERR
end

(* old version:
local
  fun conv0 ty =
    case ty of
      TyApp(Opr,Ty) => TyApp(conv Opr, conv Ty)
    | TyUniv(Btyvar,Body) => TyUniv(Btyvar, conv Body)
    | TyAbst(Btyvar,Body) => TyAbst(Btyvar, conv Body)
    | TyKindConstr{Ty,Kind} => TyKindConstr{Ty=conv Ty,Kind=Kind}
    | TyRankConstr{Ty,Rank} => TyRankConstr{Ty=conv Ty,Rank=Rank}
    | UVar (r as ref (SOMEU ty1)) => (* (r := SOMEU (conv ty1); ty) *)
                                     let val PT(ty0,_) = conv ty1 in ty0 end
    | _ => ty  (* i.e., a variable or a const *)
  and conv (ty as PT(ty0, locn)) = conv (beta_conv_ty ty)
                                   handle HOL_ERR _ => PT(conv0 ty0, locn)
in
val deep_beta_conv_ty = conv
end
*)

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
  PT(UVar (ref (SOMEU Newty)), locn) (* creates a new reference to hold the converted value *)
end
  | uvar_conv_ty conv (ty as PT(UVar (ref (NONEU _)), locn)) = ty (* unchanged *)
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

fun app_conv_ty conv ty = let
  val (Rator, Rand) = dest_app_type ty
in
  let
    val Rator' = conv Rator
  in
    mk_app_type (Rator', conv Rand) handle UNCHANGEDTY => mk_app_type (Rator', Rand)
  end handle UNCHANGEDTY => mk_app_type (Rator, conv Rand)
end

fun sub_conv_ty conv =
    try_conv_ty (app_conv_ty conv orelse_ty abs_conv_ty conv
                 orelse_ty univ_conv_ty conv orelse_ty uvar_conv_ty conv)

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

val deep_beta_conv_ty = qconv_ty (top_depth_conv_ty beta_conv_ty)



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
fun gen_unify (kind_unify:prekind -> prekind -> ('a -> 'a * unit option))
              (rank_unify:prerank -> prerank -> ('a -> 'a * unit option))
              bind c1 c2 (ty1 as PT(t1,locn1)) (ty2 as PT(t2,locn2)) e = let
  val ty1s = pretype_to_string ty1
  val ty2s = pretype_to_string ty2
  val ty1bs = pretype_to_string (deep_beta_conv_ty ty1)
  val ty2bs = pretype_to_string (deep_beta_conv_ty ty2)
  val _ = if is_debug() then print ("gen_unify " ^ ty1s
                                ^ "\n   (beta) " ^ ty1bs
                                ^ "\n      vs. " ^ ty2s
                                ^ "\n   (beta) " ^ ty2bs ^ "\n")
                        else ()
  val gen_unify = gen_unify kind_unify rank_unify bind
  val fail = fn e => (if not (is_debug()) then () else
                      print ("gen_unify fails on " ^ ty1s
                         ^ "\n               vs. " ^ ty2s ^ "\n");
                      fail e)
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
         kind_unify kd (pkind_of ty2) >>
         rank_unify rk (prank_of ty2) >>
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
(*val deep_beta_conv_ty = qconv_ty (top_depth_conv_ty beta_conv_ty)*)
(*fun qconv_ty c ty = c ty handle UNCHANGEDTY => ty*)
(*
     let val ty1' = deep_beta_conv_ty ty1
         val ty2' = deep_beta_conv_ty ty2
     in if eq ty1 ty1' andalso eq ty2 ty2'
        then m (* do m if beta_conversion did not change the types *)
        else f ty1' ty2'
     end
*)
(*
     let val (ty1',red1) = (beta_conv_ty ty1,true) handle HOL_ERR _ => (ty1,false)
         val (ty2',red2) = (beta_conv_ty ty2,true) handle HOL_ERR _ => (ty2,false)
     in if red1 orelse red2
        then f ty1' ty2'
        else m
     end
*)
in
  case (t1, t2) of
    (UVar (r as ref (NONEU(kd,rk))), _) => kind_unify kd (pkind_of ty2) >>
                                           rank_unify rk (prank_of ty2) >>
                                           bind (gen_unify c1 c2) r ty2
  | (UVar (r as ref (SOMEU t1)), t2) => gen_unify c1 c2 t1 ty2
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
       gen_unify c1 c2 ty11 ty21 >> gen_unify c1 c2 ty12 ty22 >> return ()
(*
  | (TyApp(ty11, ty12), TyApp(ty21, ty22)) =>
       beta_conv_ty_m (gen_unify c1 c2) ty1 ty2
       (gen_unify c1 c2 ty11 ty21 >> gen_unify c1 c2 ty12 ty22 >> return ())
  | (TyApp _, _) => beta_conv_ty_m (gen_unify c1 c2) ty1 ty2 fail
  | (_, TyApp _) => beta_conv_ty_m (gen_unify c1 c2) ty1 ty2 fail
*)
  | (TyUniv(ty11, ty12), TyUniv(ty21, ty22)) =>
       bvar_unify ty11 ty21 >- (fn (PT(ty11',_),PT(ty21',_)) =>
       case (ty11',ty21') of
          (Vartype tv1, Vartype tv2) =>
            gen_unify (tv1::c1) (tv2::c2) ty12 ty22
        | _ => gen_unify c1 c2 ty12 ty22)
  | (TyAbst(ty11, ty12), TyAbst(ty21, ty22)) =>
       bvar_unify ty11 ty21 >- (fn (PT(ty11',_),PT(ty21',_)) =>
       case (ty11',ty21') of
          (Vartype tv1, Vartype tv2) =>
            gen_unify (tv1::c1) (tv2::c2) ty12 ty22
        | _ => gen_unify c1 c2 ty12 ty22)
(* older version:
  | (TyUniv(ty11, ty12), TyUniv(ty21, ty22)) =>
       ((gen_unify ty11 ty21 >> gen_unify ty12 ty22) ++
        (gen_unify ty12 (type_subst [ty12 |-> ty11] ty22))) >> return ()
  | (TyAbst(ty11, ty12), TyAbst(ty21, ty22)) =>
       ((gen_unify ty11 ty21 >> gen_unify ty12 ty22) ++
        (gen_unify ty12 (type_subst [ty12 |-> ty11] ty22))) >> return ()
*)
  | _ => fail
 end e

val empty_env = ([]:(prekind option ref * prekind option) list,
                 []:(prerank option ref * prerank option) list,
                 []:(      uvartype ref * uvartype      ) list)

fun unify t1 t2 =
  let val t1' = deep_beta_conv_ty t1
      and t2' = deep_beta_conv_ty t2
      val ty1s = pretype_to_string t1
      val ty2s = pretype_to_string t2
      val ty1s' = pretype_to_string t1'
      val ty2s' = pretype_to_string t2'
      val _ = if is_debug() then print ("unify  " ^ ty1s
                                    ^ "\n(beta) " ^ ty1s'
                                    ^ "\n   vs. " ^ ty2s
                                    ^ "\n(beta) " ^ ty2s' ^ "\n")
                            else ()
  in
  case (gen_unify kind_unify rank_unify unsafe_bind [] [] t1' t2' empty_env)
   of (bindings, SOME ()) => ()
    | (_, NONE) => raise TCERR "unify" "unify failed"
                                    (* ("unify failed: " ^ pretype_to_string t1
                                    ^ "\n      versus: " ^ pretype_to_string t2) *)
  end;

fun can_unify t1 t2 = let
  val ((kind_bindings,rank_bindings,type_bindings), result) =
        gen_unify kind_unify rank_unify unsafe_bind [] [] t1 t2 empty_env
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
                  | SOME (_, v) => (r ref_equiv v) env
              end
         | UVar (ref (SOMEU t)) => (r ref_equiv t) env
         | _ => false

      fun (r ref_occurs_in (PT(value, locn))) (env as (kenv,renv,tenv)) =
        case value
         of UVar (r' as ref (NONEU _)) =>
              r = r' orelse
              let in
                case Lib.assoc1 r' tenv
                 of NONE => false
                  | SOME (_, v) => (r ref_occurs_in v) env
              end
          | UVar (ref (SOMEU t)) => (r ref_occurs_in t) env
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

fun safe_unify t1 t2 = gen_unify kind_unify rank_unify safe_bind [] [] t1 t2
end



(*---------------------------------------------------------------------------*
 * Passes over a type, turning all of the free type variables into fresh     *
 * UVars, but doing so consistently by using a pair of envs (for bound and   *
 * free), which is are alists from variable names to type variable refs.     *
 * Bound variables are not renamed, but are recognized as masking free vars. *
 *---------------------------------------------------------------------------*)

local fun replace (s,kd,rk) env =
        case Lib.assoc1 s env
         of SOME (_, r) => (env, SOME r)
          | NONE =>
              let val r = new_uvar(kd,rk)
              in ((s, r)::env, SOME r)
              end
      fun add_bvar (v as PT(Vartype (s,kd,rk), _)) benv =
              let val r = new_uvar(kd,rk)
              in ((s, r)::benv, v (*or r, if renaming bound vars*))
              end
        | add_bvar (PT(TyKindConstr {Ty,Kind}, _)) benv =
              add_bvar Ty benv
        | add_bvar (PT(TyRankConstr {Ty,Rank}, _)) benv =
              add_bvar Ty benv
        | add_bvar _ _ = raise TCERR "rename_typevars" "add_bvar: arg is not variable"
in
fun rename_tv (ty as PT(ty0, locn)) benv =
  case ty0 of
    Vartype (v as (s,kd,rk)) =>
      (case Lib.assoc1 s benv
         of SOME _ => return ty
          | NONE   => replace v)
  | TyApp (ty1, ty2) =>
      rename_tv ty1 benv >-
      (fn ty1' => rename_tv ty2 benv >-
      (fn ty2' => return (PT(TyApp(ty1', ty2'), locn))))
  | TyUniv (ty1, ty2) =>
      let val (benv',ty1') = add_bvar ty1 benv in
      rename_tv ty2 benv' >-
      (fn ty2' => return (PT(TyUniv(ty1', ty2'), locn)))
      end
  | TyAbst (ty1, ty2) =>
      let val (benv',ty1') = add_bvar ty1 benv in
      rename_tv ty2 benv' >-
      (fn ty2' => return (PT(TyUniv(ty1', ty2'), locn)))
      end
  | TyKindConstr {Ty, Kind} =>
      rename_tv Ty benv >-
      (fn Ty' => return (PT(TyKindConstr {Ty=Ty', Kind=Kind}, locn)))
  | TyRankConstr {Ty, Rank} =>
      rename_tv Ty benv >-
      (fn Ty' => return (PT(TyRankConstr {Ty=Ty', Rank=Rank}, locn)))
  | _ => return ty

fun rename_typevars ty = valOf (#2 (rename_tv ty [] []))
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

(* needs changing *)
(* eta-expansion (see "env" after end below) *is* necessary *)
fun replace_null_links (PT(ty,_)) env = let
in
  case ty of
    UVar (r as ref (NONEU(kd,rk))) => generate_new_name r (kd,rk)
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
    Vartype (s,kd,rk) => Type.mk_vartype_opr (s, Prekind.toKind kd, Prerank.toRank rk)
  | Contype {Thy,Tyop,...} => Type.mk_thy_con_type {Thy=Thy, Tyop=Tyop}
  | TyApp(ty1,ty2)  => (Type.mk_app_type  (clean ty1, clean ty2)
                          handle Feedback.HOL_ERR e =>
                            (print ("Applying " ^ type_to_string (clean ty1)
                                    ^ " to " ^ type_to_string (clean ty2) ^ "\n");
                             raise Feedback.mk_HOL_ERR "Pretype" "clean" (#message e)))
  | TyUniv (tyv,ty) => Type.mk_univ_type (clean tyv, clean ty)
  | TyAbst (tyv,ty) => Type.mk_abs_type  (clean tyv, clean ty)
  | TyKindConstr {Ty,Kind} => clean Ty
  | TyRankConstr {Ty,Rank} => clean Ty
  | _ => raise Fail "Don't expect to see links remaining at this stage of type inference"
) handle e => raise (wrap_exn "Pretype.clean" (pretype_to_string pty) e)

fun toType ty =
  let 
      val _ = replace_null_links ty (kindvars ty, tyvars ty)
  in
    clean (remove_made_links ty)
  end
  handle e => raise (wrap_exn "Pretype" "toType" e)


val fun_tyc0 = Contype{Tyop = "fun", Thy = "min",
                       Kind = Prekind.mk_arity 2, Rank = Prerank.Zerorank}

(* chase returns the effective range of an effective function type *)

fun beta_conv_ty (PT(TyApp(PT(TyAbst(bv, body), _), arg), locn)) =
    (type_subst [bv |-> arg] body
     handle e as HOL_ERR _ =>  raise wrap_exn_loc "Pretype" "beta_conv_ty" locn e)
  | beta_conv_ty (PT(_, locn)) = raise ERRloc "beta_conv_ty" locn "not a type beta redex"

fun chase (PT(TyApp(PT(TyApp(PT(tyc, _), _), _), ty), _)) =
    if eq0 tyc fun_tyc0 then ty else raise Fail "chase applied to non-function type"
  | chase (ty as PT(TyApp(PT(TyAbst(_, _), _), _), _)) =
    (chase (beta_conv_ty ty) handle _ => raise Fail "chase applied to non-function type")
  | chase (PT(UVar(ref (SOMEU ty)), _)) = chase ty
  | chase _ = raise Fail "chase applied to non-function type"


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
