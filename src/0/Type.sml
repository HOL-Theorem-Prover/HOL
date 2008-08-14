(* ===================================================================== *)
(* FILE          : Type.sml                                              *)
(* DESCRIPTION   : HOL types.                                            *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : August 26, 1991                                       *)
(* UPDATE        : October 94. Type signature implementation moved from  *)
(*                 symtab.sml, which is now gone.                        *)
(* Modified      : September 22, 1997, Ken Larsen  (functor removal)     *)
(*                 April 12, 1998, Konrad Slind                          *)
(*                 July, 2000, Konrad Slind                              *)
(* ===================================================================== *)

structure Type :> Type =
struct

(*
In *scratch*, type
(hol-set-executable mosml-executable)
or
(hol-set-executable (concat hol-home "/bin/hol.bare"))

and type Ctrl-j.

loadPath := "/usr/local/hol/hol-omega/sigobj" :: !loadPath;
app load ["Feedback","Lib","KernelTypes","Kind","KernelSig","Lexis","Polyhash",
          "Binarymap"];
*)

open Feedback Lib KernelTypes Kind;   infix |-> ##;   infixr 3 ==>;

type tyvar    = KernelTypes.tyvar;
type kind     = KernelTypes.kind;
type hol_type = KernelTypes.hol_type;
type ('a,'b)subst = ('a,'b)Lib.subst;

val ERR = mk_HOL_ERR "Type";
val WARN = HOL_WARNING "Type";


(*---------------------------------------------------------------------------
              Create the signature for HOL types
 ---------------------------------------------------------------------------*)

val typesig = KernelSig.new_table()

(*
val _ = installPP pp_kind;
*)

(*
val k0 = Type;
val k1 = Type ==> Type;
val k2 = mk_arity 2;
val k3 = (Type ==> Type) ==> (Type ==> Type);
val k4 = k2 ==> k1 ==> k2;
val k5 = k4 ==> k4 ==> k4;
val k6 = k5 ==> k5;
kind_dom_rng k0; (* should fail *)
kind_dom_rng k1;
kind_dom_rng k2;
kind_dom_rng k3;
kind_dom_rng k4;
is_arity k0;
is_arity k1;
is_arity k2;
is_arity k3;
is_arity k4;
arity_of k0;
arity_of k1;
arity_of k2;
arity_of k3; (* should fail *)
arity_of k4; (* should fail *)
*)


(*---------------------------------------------------------------------------*
 * Builtin type operators (fun, bool, ind). These are in every HOL           *
 * signature, and it is convenient to nail them down here.                   *
 *---------------------------------------------------------------------------*)

local open KernelSig
in
val fun_tyid  = insert(typesig, {Thy = "min", Name = "fun"},  (mk_arity 2:kind, 0))
val bool_tyid = insert(typesig, {Thy = "min", Name = "bool"}, (mk_arity 0, 0))
val ind_tyid  = insert(typesig, {Thy = "min", Name = "ind"},  (mk_arity 0, 0))
val fun_tyc  = ( fun_tyid, mk_arity 2, 0)
val bool_tyc = (bool_tyid, mk_arity 0, 0)
val ind_tyc  = ( ind_tyid, mk_arity 0, 0)
end

(* For testing:

local open TypeSig
in
val foo_tyid  = insert(typesig, {Thy = "min", Name = "foo"},  (k3, 0))
val bar_tyid  = insert(typesig, {Thy = "min", Name = "bar"},  (k4, 1))
val foo_tyc  = ( foo_tyid, k3, 0)
val bar_tyc  = ( bar_tyid, k4, 1)
end;
*)

(*---------------------------------------------------------------------------
        Some basic values
 ---------------------------------------------------------------------------*)

val bool = TyCon bool_tyc
val ind  = TyCon ind_tyc;

(*
val foo  = TyCon foo_tyc
val bar  = TyCon bar_tyc;
*)


fun same_tyconst (id1,_,_) (id2,_,_) = id1 = id2


(*---------------------------------------------------------------------------
       Function types
 ---------------------------------------------------------------------------*)

infixr 3 -->;
fun (X --> Y) = TyApp (TyApp (TyCon fun_tyc, X), Y);

local
fun dom_of (TyApp(TyCon tyc, Y)) =
      if same_tyconst tyc fun_tyc then Y
      else raise ERR "dom_rng" "not a function type"
  | dom_of _ = raise ERR "dom_rng" "not a function type"
in
fun dom_rng (TyApp(funX, Y)) = (dom_of funX, Y)
  | dom_rng _ = raise ERR "dom_rng" "not a function type"
end;

(*
val ty0 = bool
val ty1 = ind --> bool
val ty2 = ind --> ind --> bool
val ty3 = ty1 --> ty1;
val ty4 = foo --> bar; (* not well-kinded *)
val ty5 = TyApp(bar, TyCon fun_tyc); (* well-kinded *)
val ty6 = TyAll(("'a",mk_arity 0,0), TyBv 0 --> bool);
val ty7 = TyAbs(("'a",mk_arity 0,0), TyBv 0 --> bool);
dom_rng ty0; (* should fail *)
dom_rng ty1;
dom_rng ty2;
dom_rng ty3;
dom_rng ty4;
dom_rng ty5; (* should fail *)
dom_rng ty6; (* should fail *)
dom_rng ty7; (* should fail *)
*)


(*---------------------------------------------------------------------------*
 * Computing the kind of a type, assuming it is well-kinded.                 *
 *---------------------------------------------------------------------------*)

local fun lookup 0 (kd::_)  = kd
        | lookup n (_::rst) = lookup (n-1) rst
        | lookup _ []       = raise ERR "kind_of" "lookup"
      fun kd_of (TyFv (_,kd,_)) _        = kd
        | kd_of (TyCon(_,kd,_)) _        = kd
        | kd_of (TyBv i) E               = lookup i E
        | kd_of (TyApp(Opr,_)) E         = snd(kind_dom_rng (kd_of Opr E))
        | kd_of (TyAll((_,Kd,_),Body)) E = kd_of Body (Kd::E)
        | kd_of (TyAbs((_,Kd,_),Body)) E = Kd ==> kd_of Body (Kd::E)
in
fun kind_of ty = kd_of ty []
end;

(*
kind_of ty0;
kind_of ty1;
kind_of ty2;
kind_of ty3;
kind_of ty4;
kind_of ty5;
kind_of ty6;
kind_of ty7;
*)

(*---------------------------------------------------------------------------*
 * Computing the rank of a type.                                             *
 *---------------------------------------------------------------------------*)

local val max = Int.max
      fun lookup 0 (rk::_)  = rk
        | lookup n (_::rst) = lookup (n-1) rst
        | lookup _ []       = raise ERR "rank_of" "lookup"
in
      fun rk_of (TyFv (_,_,rk)) _        = rk
        | rk_of (TyCon(_,_,rk)) _        = rk
        | rk_of (TyBv i) E               = lookup i E
        | rk_of (TyApp(opr, ty)) E       = max (rk_of opr E, rk_of ty E)
        | rk_of (TyAll((_,_,rk),Body)) E = max (rk, rk_of Body (rk::E)) + 1
        | rk_of (TyAbs((_,_,rk),Body)) E = max (rk, rk_of Body (rk::E))
fun rank_of ty = rk_of ty []
end;

(*
rank_of ty0;
rank_of ty1;
rank_of ty2;
rank_of ty3;
rank_of ty4;
rank_of ty5;
rank_of ty6;
rank_of ty7;
*)

fun rank_of_univ_dom (TyAll((_,_,rk),_)) = rk
  | rank_of_univ_dom _ = raise ERR "rank_of_univ_dom" "not a universal type"

(*---------------------------------------------------------------------------*
 * Computing the kind of a type, not assuming it is well-kinded.             *
 *---------------------------------------------------------------------------*)

local fun lookup 0 (kd::_)  = kd
        | lookup n (_::rst) = lookup (n-1) rst
        | lookup _ []       = raise ERR "check_kind_of" "lookup"
      fun kd_of (TyFv (_,kd,rk)) _        = kd
        | kd_of (TyCon(_,kd,rk)) _        = kd
        | kd_of (TyBv i) E                = lookup i E
        | kd_of (TyApp(Opr,Ty)) E         =
             let val (dom,rng) = kind_dom_rng (kd_of Opr E)
                                 handle HOL_ERR _ =>
                     raise ERR "check_kind_of" "type is not well-kinded"
             in if dom = kd_of Ty E then rng
                else raise ERR "check_kind_of" "type is not well-kinded"
             end
        | kd_of (TyAll((_,kd,rk),Body)) E = kd_of Body (kd::E)
        | kd_of (TyAbs((_,kd,rk),Body)) E = kd ==> kd_of Body (kd::E)
in
fun check_kind_of ty = kd_of ty []
end;

(*
check_kind_of ty0;
check_kind_of ty1;
check_kind_of ty2;
check_kind_of ty3;
check_kind_of ty4; (* should fail *)
check_kind_of ty5;
check_kind_of ty6;
check_kind_of ty7;
*)

(*---------------------------------------------------------------------------*
 * Checking that a type is well-kinded.                                      *
 * This fn should never be needed, as long as the type constructors check.   *
 *---------------------------------------------------------------------------*)

fun is_well_kinded ty = (check_kind_of ty; true) handle HOL_ERR _ => false

(*
well_kinded ty0;
well_kinded ty1;
well_kinded ty2;
well_kinded ty3;
well_kinded ty4; (* false *)
well_kinded ty5;
well_kinded ty6;
well_kinded ty7;
*)

(*---------------------------------------------------------------------------*
 * Increasing the rank of a type.                                            *
 *---------------------------------------------------------------------------*)

fun inst_rank i ty =
  let fun inc_rk (TyFv (s,kd,rk))        = TyFv (s,kd,rk+i)
        | inc_rk (TyCon(s,kd,rk))        = TyCon(s,kd,rk (* +i *) ) (* maybe later *)
        | inc_rk (ty as TyBv _)          = ty
        | inc_rk (TyApp(opr, ty))        = TyApp(inc_rk opr, inc_rk ty)
        | inc_rk (TyAll((s,kd,rk),Body)) = TyAll((s,kd,rk+i), inc_rk Body)
        | inc_rk (TyAbs((s,kd,rk),Body)) = TyAbs((s,kd,rk+i), inc_rk Body)
  in if i = 0 then ty
     else if i < 0 then raise ERR "inst_rank" "increment is negative"
     else inc_rk ty
  end;


(*---------------------------------------------------------------------------
                Discriminators
 ---------------------------------------------------------------------------*)

fun is_bvartype  (TyBv  _) = true | is_bvartype  _ = false;
fun is_vartype   (TyFv  _) = true | is_vartype   _ = false;
fun is_con_type  (TyCon _) = true | is_con_type  _ = false;
fun is_type      (TyApp (opr,_)) = is_type opr
  | is_type      (TyCon _) = true
  | is_type      _ = false;
fun is_app_type  (TyApp _) = true
  | is_app_type  _ = false;
fun is_abs_type  (TyAbs _) = true
  | is_abs_type  _ = false;
fun is_univ_type (TyAll _) = true
  | is_univ_type _ = false;

(*---------------------------------------------------------------------------*
 * Types, as seen by the user, should satisfy exactly one of                 *
 * is_vartype, is_con_type, is_app_type, is_abs_type, or is_univ_type.       *
 * Legacy types will be seen as exactly one of is_vartype or is_type.        *
 *---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------*
 * The free type variables in a type.  Tail recursive (from Ken Larsen).     *
 *---------------------------------------------------------------------------*)

local fun TV (v as TyFv _) A k    = k (Lib.insert v A)
        | TV (TyApp(opr, ty)) A k = TV opr A (fn q => TV ty q k)
        | TV (TyAll(_,ty)) A k    = TV ty A k
        | TV (TyAbs(_,ty)) A k    = TV ty A k
        | TV _ A k = k A
      and TVl (ty::tys) A k       = TV ty A (fn q => TVl tys q k)
        | TVl _ A k = k A
in
fun type_vars ty = rev(TV ty [] Lib.I)
fun type_varsl L = rev(TVl L [] Lib.I)
end;

(*---------------------------------------------------------------------------*
 * All the type variables in a type.  Tail recursive (from Ken Larsen).      *
 *---------------------------------------------------------------------------*)

local fun ATV (v as TyFv _) A k    = k (Lib.insert v A)
        | ATV (TyApp(opr, ty)) A k = ATV opr A (fn q => ATV ty q k)
        | ATV (TyAll(bv,ty)) A k   = ATV (TyFv bv) A (fn q => ATV ty q k)
        | ATV (TyAbs(bv,ty)) A k   = ATV (TyFv bv) A (fn q => ATV ty q k)
        | ATV _ A k = k A
      and ATVl (ty::tys) A k       = ATV ty A (fn q => ATVl tys q k)
        | ATVl _ A k = k A
in
fun all_type_vars ty = rev(ATV ty [] Lib.I)
fun all_type_varsl L = rev(ATVl L [] Lib.I)
end;

(*---------------------------------------------------------------------------*
 * The free type variables of a type, in textual order.                      *
 *---------------------------------------------------------------------------*)

fun type_vars_lr ty =
  let fun TV ((v as TyFv _)::t) A    = TV t (Lib.insert v A)
        | TV (TyApp(opr, ty)::t) A   = TV (opr::ty::t) A
        | TV (TyAll(_,ty)::t) A      = TV (ty::t) A
        | TV (TyAbs(_,ty)::t) A      = TV (ty::t) A
        | TV (_::t) A = TV t A
        | TV [] A = rev A
  in
     TV [ty] []
  end;


(*---------------------------------------------------------------------------
     Support for efficient sets of type variables
 ---------------------------------------------------------------------------*)

val kind_rank_compare = Lib.pair_compare(kind_compare, Int.compare);

fun tyvar_compare ((s1,k1,rk1), (s2,k2,rk2)) =
       (case String.compare (s1,s2)
         of EQUAL => kind_rank_compare ((k1,rk1),(k2,rk2))
          | x => x)

val empty_tyvarset = HOLset.empty tyvar_compare
fun tyvar_eq t1 t2 = tyvar_compare(t1,t2) = EQUAL;

fun type_var_compare (TyFv u, TyFv v) = tyvar_compare (u,v)
  | type_var_compare _ =raise ERR "type_var_compare" "variables required";

fun type_con_compare (TyCon(c1,k1,rk1), TyCon(c2,k2,rk2)) =
       (case KernelSig.id_compare (c1,c2)
         of EQUAL => kind_rank_compare ((k1,rk1),(k2,rk2))
          | x => x)
  | type_con_compare _ =raise ERR "type_con_compare" "constants required";

(* ----------------------------------------------------------------------
    A total ordering on types that respects alpha equivalence.
    TyFv < TyBv < TyCon < TyApp < TyAll < TyAbs
   ---------------------------------------------------------------------- *)

fun compare p =
    if Portable.pointer_eq p then EQUAL else
    case p of
      (u as TyFv _, v as TyFv _)   => type_var_compare (u,v)
    | (TyFv _, _)                  => LESS
    | (TyBv _, TyFv _)             => GREATER
    | (TyBv i, TyBv j)             => Int.compare (i,j)
    | (TyBv _, _)                  => LESS
    | (TyCon _, TyFv _)            => GREATER
    | (TyCon _, TyBv _)            => GREATER
    | (u as TyCon _, v as TyCon _) => type_con_compare (u,v)
    | (TyCon _, _)                 => LESS
    | (TyApp _, TyFv _)            => GREATER
    | (TyApp _, TyBv _)            => GREATER
    | (TyApp _, TyCon _)           => GREATER
    | (TyApp p1, TyApp p2)         => Lib.pair_compare(compare,compare)(p1,p2)
    | (TyApp _, _)                 => LESS
    | (TyAll _, TyAbs _)           => LESS
    | (TyAll((_,k1,rk1),ty1),
       TyAll((_,k2,rk2),ty2))      =>
                                 Lib.pair_compare(kind_rank_compare,compare)
                                                 (((k1,rk1),ty1),((k2,rk2),ty2))
    | (TyAll _, _)                 => GREATER
    | (TyAbs((_,k1,rk1),ty1),
       TyAbs((_,k2,rk2),ty2))      =>
                                 Lib.pair_compare(kind_rank_compare,compare)
                                                 (((k1,rk1),ty1),((k2,rk2),ty2))
    | (TyAbs _, _)                 => GREATER
;

val empty_tyset = HOLset.empty compare
fun type_eq t1 t2 = compare(t1,t2) = EQUAL;


(*---------------------------------------------------------------------------
        Free type variables of a type. Tail recursive. Returns a set.
 ---------------------------------------------------------------------------*)

fun TVL [] A = A
  | TVL ((v as TyFv _)::rst) A   = TVL rst (HOLset.add(A,v))
  | TVL (TyApp(opr,ty)::rst) A   = TVL (opr::ty::rst) A
  | TVL (TyAll(_,Body)::rst) A   = TVL (Body::rst) A
  | TVL (TyAbs(_,Body)::rst) A   = TVL (Body::rst) A
  | TVL (_::rst) A = TVL rst A

fun type_vars ty = HOLset.listItems (TVL [ty] empty_tyset)
fun type_varsl tys = HOLset.listItems (TVL tys empty_tyset);

(* ----------------------------------------------------------------------
    type_var_in ty TY : does ty occur free in TY?
   ---------------------------------------------------------------------- *)

fun type_var_in ty =
   let fun f1 (TyApp(opr,ty)) = (f2 opr) orelse (f2 ty)
         | f1 (TyAll(_,Body)) = f2 Body
         | f1 (TyAbs(_,Body)) = f2 Body
         | f1 _ = false
       and f2 t = type_eq t ty orelse f1 t
   in f2
   end;


(*---------------------------------------------------------------------------*
 *         Type variables                                                    *
 *---------------------------------------------------------------------------*)

val alpha  = TyFv ("'a",mk_arity 0,0)
val beta   = TyFv ("'b",mk_arity 0,0)
val gamma  = TyFv ("'c",mk_arity 0,0)
val delta  = TyFv ("'d",mk_arity 0,0)
val etyvar = TyFv ("'e",mk_arity 0,0)
val ftyvar = TyFv ("'f",mk_arity 0,0)

(*
compare(alpha, alpha);
compare(alpha, beta);
compare(beta, alpha);
val ty6 = alpha --> beta --> gamma;
val ty7 = alpha --> bool --> gamma;
val ty8 = TyAll(("'a",mk_arity 0,0),TyBv 0);
val ty9 = TyAll(("'a",mk_arity 0,0),TyAll(("'b",mk_arity 0,0),
                         TyBv 0 --> gamma --> TyBv 1));
type_vars ty6;
type_vars ty7;
type_vars ty8;
type_vars ty9;
type_varsl [ty7,ty8,ty9];
*)

val varcomplain = ref true
val _ = register_btrace ("Vartype Format Complaint", varcomplain)

fun mk_vartype_opr ("'a", Type, 0) = alpha
  | mk_vartype_opr ("'b", Type, 0) = beta
  | mk_vartype_opr ("'c", Type, 0) = gamma
  | mk_vartype_opr ("'d", Type, 0) = delta
  | mk_vartype_opr ("'e", Type, 0) = etyvar
  | mk_vartype_opr ("'f", Type, 0) = ftyvar
  | mk_vartype_opr (s, kind, rank) =
                if rank < 0 then
                        raise ERR "mk_vartype_opr" "negative rank"
                else
                if Lexis.allowed_user_type_var s
                then TyFv (s, kind, rank)
                else (if !varcomplain then
                        WARN "mk_vartype_opr" ("non-standard syntax: " ^ s)
                      else (); TyFv (s, kind, rank))

fun mk_vartype s = mk_vartype_opr (s, Type, 0);

fun inST s = let
  fun foldthis({Thy,Name},_,acc) = (acc orelse (Name = s))
in
  KernelSig.foldl foldthis false typesig
end

fun mk_primed_vartype_opr (Name, Kind, Rank) =
  let val next = Lexis.tyvar_vary
      fun spin s = if inST s then spin (next s) else s
  in mk_vartype_opr(spin Name, Kind, Rank)
  end;

fun mk_primed_vartype s = mk_primed_vartype_opr (s, Type, 0);

(*---------------------------------------------------------------------------*
 *   "gen_tyvars" are a Lisp-style "gensym" for HOL variables.               *
 *---------------------------------------------------------------------------*)

local val gen_tyvar_prefix = "%%gen_tyvar%%"
      fun num2name i = gen_tyvar_prefix^Lib.int_to_string i
      val nameStrm = Lib.mk_istream (fn x => x+1) 0 num2name
in
fun gen_tyopvar (Kind,Rank) =
       if Rank < 0 then
               raise ERR "gen_tyopvar" "negative rank"
       else
       TyFv(state(next nameStrm), Kind, Rank)
fun gen_tyvar () = gen_tyopvar (Type, 0)

fun is_gen_tyvar (TyFv(Name,_,_)) =
        String.isPrefix gen_tyvar_prefix Name
  | is_gen_tyvar _ = false
end;

(*
val ty10 = gen_tyvar ();
val ty11 = gen_tyopvar (k2,3);
is_gen_tyvar ty9;
is_gen_tyvar alpha;
is_gen_tyvar ty10;
is_gen_tyvar ty11;
*)


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
  let fun var_name (TyFv(Name,_,_)) = Name
        | var_name _ = raise ERR caller "not a variable"
      fun vary vlist (TyFv(Name,Kind,Rank)) =
          let val L = map var_name vlist
              val next = Lexis.gen_variant Lexis.tyvar_vary L
              fun loop name =
                 let val s = next name
                 in if P s then loop s else s
                 end
          in mk_vartype_opr(loop Name, Kind, Rank)
          end
        | vary _ _ = raise ERR caller "2nd argument should be a variable"
  in vary
  end;

val variant_type       = gen_variant inST "variant_type"
val prim_variant_type  = gen_variant (K false) "prim_variant_type";



fun dest_vartype_opr (TyFv (s,kind,rank)) =
           (s,kind,rank)
  | dest_vartype_opr _ =
           raise ERR "dest_vartype_opr" "not a type variable";

fun dest_vartype (TyFv (s,Type,0)) = s
  | dest_vartype (TyFv (s,Type,rank)) =
           raise ERR "dest_vartype" "non-zero rank - use dest_vartype_opr"
  | dest_vartype (TyFv (s,_,_)) =
           raise ERR "dest_vartype" "type operator kind - use dest_vartype_opr"
  | dest_vartype _ = raise ERR "dest_vartype" "not a type variable";

(*
dest_vartype ty10;
dest_vartype ty11;
*)


fun variant_tyvar tys tyv =
       let val ty0 = TyFv tyv
           val ty = variant_type tys ty0
        in dest_vartype_opr ty
       end;

(*---------------------------------------------------------------------------*
 * Create a compound type, in a specific segment, and in the current theory. *
 *---------------------------------------------------------------------------*)

local
fun dest_con_type (TyCon (tyc,kd,rk)) = (KernelSig.name_of tyc,kd,rk)
  | dest_con_type _ = raise ERR "dest_con_type" "not a constant type";
in
fun make_app_type Opr Arg (fnstr,name) =
  let val name = if name <> "" then name
                 else if is_con_type Opr then #1(dest_con_type Opr)
                 else if is_vartype Opr then #1(dest_vartype_opr Opr)
                 else "<not a type constant or variable>"
      val (dom,rng) = kind_dom_rng (kind_of Opr)
                      handle HOL_ERR e =>
                        raise ERR fnstr (String.concat
         ["type not well-kinded: ", name,
          " is not a type operator, but is applied as one"])
      val kn = kind_of Arg
  in if dom = kn then TyApp(Opr,Arg) else
     raise ERR fnstr (String.concat
         ["type not well-kinded: ", name, " needs kind ", kind_to_string dom,
          ", but was given kind ", kind_to_string kn])
  end
end;

fun list_make_app_type Opr Args (fnstr,name) =
    List.foldl (fn (Arg,acc) => make_app_type acc Arg (fnstr,name)) Opr Args

fun make_type tyc Args (fnstr,name) =
  list_make_app_type (TyCon tyc) Args (fnstr,name);

fun mk_tyconst (id,(kind,rank)) = (id,kind,rank) :tyconst

fun mk_thy_type {Thy,Tyop,Args} = let
  open KernelSig
  val knm = {Thy=Thy, Name = Tyop}
in
  case peek(typesig, {Thy=Thy,Name=Tyop}) of
    SOME const => make_type (mk_tyconst const) Args
                            ("mk_thy_type", name_toString knm)
  | NONE => raise ERR "mk_thy_type"
                      ("the type operator "^quote Tyop^
                       " has not been declared in theory "^quote Thy^".")
end

fun mk_thy_con_type {Thy,Tyop} = let
  open KernelSig
  val knm = {Thy=Thy, Name = Tyop}
in
  case peek(typesig,{Thy=Thy,Name=Tyop}) of
    SOME const => TyCon (mk_tyconst const)
  | NONE => raise ERR "mk_thy_con_type"
                ("the type operator "^quote Tyop^
                 " has not been declared in theory "^quote Thy^".")
end

fun decls nm = let
  fun foldthis({Thy,Name},_,acc) = if Name = nm then
                                     {Tyop=Name,Thy=Thy} :: acc
                                   else acc
in
  KernelSig.foldl foldthis [] typesig
end

local
  fun first_decl Tyop = let
    fun foldthis({Thy,Name},tycon,acc) =
        if Name = Tyop then mk_tyconst tycon :: acc
        else acc
  in
    case KernelSig.foldl foldthis [] typesig of
      [] => raise ERR "mk_type" (Lib.quote Tyop^" has not been declared")
    | [c] => c
    | c::_ => (WARN "mk_type" "more than one possibility"; c)
  end
in

fun mk_con_type Tyop = TyCon (first_decl Tyop);

fun mk_app_type (Opr,Arg) = make_app_type Opr Arg ("mk_app_type","");

fun list_mk_app_type (Opr,Args) =
    list_make_app_type Opr Args ("list_mk_app_type","");

fun mk_type (Tyop,Args) =
    make_type (first_decl Tyop) Args ("mk_type",Tyop);
end

(*
mk_con_type "fun";
mk_type("fun",[alpha,beta]);
mk_type("bool",[]);
mk_app_type(mk_con_type "fun", mk_con_type "bool");
mk_app_type(mk_con_type "fun", mk_con_type "fun"); (* fails *)
mk_type("fun",[foo,bar]); (* fails *)
mk_type("fun",[alpha,bar]); (* fails *)
mk_app_type(mk_app_type(mk_con_type "fun", mk_con_type "ind"),
            mk_con_type "bool");
val ty12 =
   list_mk_app_type(mk_con_type "fun",[mk_con_type "ind",mk_con_type "bool"]);
*)

(*---------------------------------------------------------------------------*
 * Take a (TyApp(TyCon)) type apart.                                         *
 *---------------------------------------------------------------------------*)

local open KernelTypes KernelSig
fun break_ty0 f acc (TyCon c) = (c,acc)
  | break_ty0 f acc (TyApp (Opr,Arg)) = break_ty0 f (Arg::acc) Opr
  | break_ty0 f _ _ = raise ERR f "not a sequence of type applications of a \
                                  \type constant"
fun break_ty f ty = break_ty0 f [] ty
in
fun break_type ty = break_ty "break_type" ty;

fun dest_thy_type_opr ty =
       let val ((tyc,kd,rk),A) = break_ty "dest_thy_type_opr" ty
       in
        {Thy=seg_of tyc,Tyop=name_of tyc,Kind=kd,Rank=rk,Args=A}
       end;

fun dest_thy_type ty =
       let val ((tyc,kd,rk),A) = break_ty "dest_thy_type" ty
       in
        {Thy=seg_of tyc,Tyop=name_of tyc,Args=A}
       end;

fun dest_type_opr ty =
       let val ((tyc,kd,rk),A) = break_ty "dest_type_opr" ty
       in (name_of tyc, kd, rk, A)
       end;

fun dest_type ty =
       let val ((tyc,kd,rk),A) = break_ty "dest_type" ty
       in (name_of tyc, A)
       end;
end;

fun dest_con_type (TyCon (tyc,kd,rk)) = (KernelSig.name_of tyc,kd,rk)
  | dest_con_type _ = raise ERR "dest_con_type" "not a constant type";

fun dest_thy_con_type (TyCon (tyc,kd,rk)) =
      {Thy=KernelSig.seg_of tyc,Tyop=KernelSig.name_of tyc,Kind=kd,Rank=rk}
  | dest_thy_con_type _ = raise ERR "dest_thy_con_type" "not a constant type";

fun dest_app_type (TyApp (Opr,Ty)) = (Opr,Ty)
  | dest_app_type _ = raise ERR "dest_app_type" "not a type application";

fun strip_app_type ty =
   let fun strip (TyApp (Opr,Ty)) A = strip Opr (Ty::A)
         | strip ty A = (ty,A)
   in strip ty []
   end

(*
dest_thy_type_opr ty12;
dest_thy_type ty12;
dest_type_opr ty12;
dest_type ty12;
*)

(*---------------------------------------------------------------------------*
 * Return kind or arity of putative type operator                            *
 *---------------------------------------------------------------------------*)

fun op_kind {Thy,Tyop} =
    case KernelSig.peek(typesig,{Thy=Thy,Name=Tyop}) of
      SOME (id, (kind, rank)) => SOME kind
    | NONE => NONE

fun op_arity r = case op_kind r
                  of SOME kind => (SOME (arity_of kind)
                                   handle HOL_ERR _ => NONE)
                   | NONE      => NONE

(*---------------------------------------------------------------------------*
 * Return rank of putative type operator                                     *
 *---------------------------------------------------------------------------*)

fun op_rank {Thy,Tyop} =
    case KernelSig.peek(typesig,{Thy=Thy,Name=Tyop}) of
      SOME (id, (kind, rank)) => SOME rank
    | NONE => NONE

(*---------------------------------------------------------------------------
       Declared types in a theory segment
 ---------------------------------------------------------------------------*)

fun thy_types s = let
  fun xlate (knm, (id,(kind,rank))) =
        (KernelSig.name_of id, arity_of kind handle HOL_ERR _ =>
                raise ERR "thy_types" "non-arity kind in theory - use thy_type_oprs"
        )
in
  map xlate (KernelSig.listThy typesig s)
end;

fun thy_type_oprs s = let
  fun xlate (knm, (id,(kind,rank))) =
            (KernelSig.name_of id, kind, rank)
  in map xlate (KernelSig.listThy typesig s)
  end;

(*---------------------------------------------------------------------------*
 *                  Alpha conversion                                         *
 *---------------------------------------------------------------------------*)

fun rename_btyvar s t =
    case t of
      TyAll((_, kind, rank), Body) => TyAll((s, kind, rank), Body)
    | TyAbs((_, kind, rank), Body) => TyAbs((s, kind, rank), Body)
    | _ => raise ERR "rename_btyvar" "not a universal type or type abstraction";


local val EQ = Portable.pointer_eq
in
fun aconv_ty t1 t2 = EQ(t1,t2) orelse
 case(t1,t2)
  of (u as TyFv _, v as TyFv _ ) => type_var_compare(u,v) = EQUAL
   | (u as TyCon _,v as TyCon _) => type_con_compare(u,v) = EQUAL
   | (TyApp(p,t1),TyApp(q,t2)) => aconv_ty p q andalso aconv_ty t1 t2
   | (TyAll((_,k1,r1),t1),
      TyAll((_,k2,r2),t2)) => k1 = k2 andalso r1 = r2 andalso aconv_ty t1 t2
   | (TyAbs((_,k1,r1),t1),
      TyAbs((_,k2,r2),t2)) => k1 = k2 andalso r1 = r2 andalso aconv_ty t1 t2
   | (M,N)       => (M=N)
end;


(*---------------------------------------------------------------------------*
 * Universal types                                                           *
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
       Making universal types. list_mk_type_binder is a relatively
       efficient version for making types with many consecutive
       universal type quantifications.
  ---------------------------------------------------------------------------*)

local val FORMAT = ERR "list_mk_univ_type_binder"
   "expected first arg to be a type constant of type :(<ty>_1 -> <ty>_2) -> <ty>_3"
   fun check_opt NONE = Lib.I
     | check_opt (SOME c) = (fn abs => mk_app_type (c, abs))
       (* or,
        if not(is_con_type c) then raise FORMAT
        else case total (fst o kind_dom_rng o fst o kind_dom_rng o kind_of) c
              of NONE => raise FORMAT
               | SOME kn => (fn abs =>
                   let val dom = fst(kind_dom_rng(kind_of abs))
                   in mk_app_type ( (* inst[kn |-> dom] *) c, abs)
                   end)
       *)
in
fun list_mk_univ_type_binder opt =
 let val f = check_opt opt
 in fn (vlist,ty)
 => if not (all is_vartype vlist) then raise ERR "list_mk_univ_type_binder" ""
    else
  let open Polyhash
     val varmap = mkPolyTable(length vlist, Fail "varmap")
     fun enum [] _ A = A
       | enum (TyFv h::t) i A = (insert varmap (h,i); enum t (i-1) (h::A))
       | enum _ _ _ = raise ERR "enum" "non-variable given as bound variable"
     val rvlist = enum vlist (length vlist - 1) []
     fun lookup v vmap = case peek vmap v of NONE => TyFv v | SOME i => TyBv i
     fun increment vmap = transform (fn x => x+1) vmap
     fun bind (TyFv v) vmap k = k (lookup v vmap)
       | bind (TyApp(opr,ty)) vmap k = bind opr vmap (fn opr' =>
                                       bind ty  vmap (fn ty'  =>
                                          k (TyApp(opr',ty'))))
       | bind (TyAll(a,ty)) vmap k  = bind ty (increment vmap)
                                          (fn q => k (TyAll(a,q)))
       | bind (TyAbs(a,ty)) vmap k  = bind ty (increment vmap)
                                          (fn q => k (TyAbs(a,q)))
       | bind t vmap k = k t
  in
     rev_itlist (fn v => fn B => f(TyAll(v,B))) rvlist (bind ty varmap I)
  end
  handle e => raise wrap_exn "Type" "list_mk_univ_type_binder" e
 end
end;

val list_mk_univ_type = list_mk_univ_type_binder NONE;

fun mk_univ_type (Bvar as TyFv tyvar, Body) =
    let fun bind (TyFv v) i            = if v=tyvar then TyBv i else TyFv v
          | bind (TyApp(opr,ty)) i     = TyApp(bind opr i, bind ty i)
          | bind (TyAll(Bvar,Body)) i  = TyAll(Bvar, bind Body (i+1))
          | bind (TyAbs(Bvar,Body)) i  = TyAbs(Bvar, bind Body (i+1))
          | bind t _ = t
    in
      TyAll(tyvar, bind Body 0)
    end
  | mk_univ_type _ = raise ERR "mk_univ_type" "bound variable arg not a variable";


(*---------------------------------------------------------------------------*
 * Type abstractionss                                                        *
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
       Making type abstractions. list_mk_type_binder is a relatively
       efficient version for making types with many consecutive
       type abstractions.
  ---------------------------------------------------------------------------*)

local val FORMAT = ERR "list_mk_type_binder"
   "expected first arg to be a type constant of type :(<ty>_1 -> <ty>_2) -> <ty>_3"
   fun check_opt NONE = Lib.I
     | check_opt (SOME c) = (fn abs => mk_app_type (c, abs))
       (* or,
        if not(is_con_type c) then raise FORMAT
        else case total (fst o kind_dom_rng o fst o kind_dom_rng o kind_of) c
              of NONE => raise FORMAT
               | SOME kn => (fn abs =>
                   let val dom = fst(kind_dom_rng(kind_of abs))
                   in mk_app_type ( (* inst[kn |-> dom] *) c, abs)
                   end)
       *)
in
fun list_mk_type_binder opt =
 let val f = check_opt opt
 in fn (vlist,ty)
 => if not (all is_vartype vlist) then raise ERR "list_mk_type_binder" ""
    else
  let open Polyhash
     val varmap = mkPolyTable(length vlist, Fail "varmap")
     fun enum [] _ A = A
       | enum (TyFv h::t) i A = (insert varmap (h,i); enum t (i-1) (h::A))
       | enum _ _ _ = raise ERR "enum" "non-variable given as bound variable"
     val rvlist = enum vlist (length vlist - 1) []
     fun lookup v vmap = case peek vmap v of NONE => TyFv v | SOME i => TyBv i
     fun increment vmap = transform (fn x => x+1) vmap
     fun bind (TyFv v) vmap k = k (lookup v vmap)
       | bind (TyApp(opr,ty)) vmap k = bind opr vmap (fn opr' =>
                                       bind ty  vmap (fn ty'  =>
                                          k (TyApp(opr',ty'))))
       | bind (TyAll(a,ty)) vmap k  = bind ty (increment vmap)
                                          (fn q => k (TyAll(a,q)))
       | bind (TyAbs(a,ty)) vmap k  = bind ty (increment vmap)
                                          (fn q => k (TyAbs(a,q)))
       | bind t vmap k = k t
  in
     rev_itlist (fn v => fn B => f(TyAbs(v,B))) rvlist (bind ty varmap I)
  end
  handle e => raise wrap_exn "Type" "list_mk_type_binder" e
 end
end;

val list_mk_abs_type = list_mk_type_binder NONE;

fun mk_abs_type (Bvar as TyFv tyvar, Body) =
    let fun bind (TyFv v) i            = if v=tyvar then TyBv i else TyFv v
          | bind (TyApp(opr,ty)) i     = TyApp(bind opr i, bind ty i)
          | bind (TyAll(Bvar,Body)) i  = TyAll(Bvar, bind Body (i+1))
          | bind (TyAbs(Bvar,Body)) i  = TyAbs(Bvar, bind Body (i+1))
          | bind t _ = t
    in
      TyAbs(tyvar, bind Body 0)
    end
  | mk_abs_type _ = raise ERR "mk_univ_type" "bound variable arg not a variable";


(*---------------------------------------------------------------------------
            Taking types apart

    These operations are all easy, except for taking apart multiple universal
    types or type abstractions. It can happen, via beta-conversion or substitution,
    or instantiation, that a free type variable is bound by the scope. One
    of the tasks of strip_univ_type is to sort the resulting mess out.
    strip_univ_type works by first classifying all the free type variables in
    the body as being captured by the prefix bindings or not. Each capturing
    prefix type binder is then renamed until it doesn't capture. Then we go
    through the body and replace the dB indices of the prefix with the
    corresponding free type variables. These may in fact fall under another
    type binder; the renaming of that will, if necessary, get done if that
    type binder is taken apart (by a subsequent dest/strip_type_binder).
 ---------------------------------------------------------------------------*)

local fun peel f ty A =
            case f ty of
              SOME(TyAll(v,M)) => peel f M (v::A)
            | otherwise => (A,ty)
      datatype occtype = PREFIX of int | BODY
      fun array_to_revlist A =
        let val top = Array.length A - 1
            fun For i B = if i>top then B else For (i+1) (Array.sub(A,i)::B)
        in For 0 []
        end
      val vi_empty = HOLset.empty (fn ((v1,i1),(v2,i2)) => tyvar_compare(v1,v2))
      fun add_vi viset vi =
         if HOLset.member(viset,vi) then viset else HOLset.add(viset,vi)
in
fun strip_univ_binder opt =
 let val f =
         case opt of
           NONE => (fn (t as TyAll _) => SOME t
                     | other => NONE)
         | SOME c => (fn t => let val (name,args) = dest_type t
                              in if name = c
                                 then SOME (mk_type(name, args))
                                 else NONE
                              end handle HOL_ERR _ => NONE)
 in fn ty =>
   let val (prefixl,body) = peel f ty []
     val prefix = Array.fromList prefixl
     val vmap = curry Array.sub prefix
     val (insertAVbody,insertAVprefix,lookAV,dupls) =
        let open Polyhash  (* AV is hashtable  of (var,occtype) elems *)
            val AV = mkPolyTable(Array.length prefix, Fail"AV")
            fun insertl [] _ dupls = dupls
              | insertl (x::rst) i dupls =
                  let val n =  #1 x (* fst(dest_var x) *)
                  in case peekInsert AV (n,PREFIX i)
                      of NONE => insertl rst (i+1) dupls
                       | SOME _ => insertl rst (i+1) ((x,i)::dupls)
                  end
            val dupls = insertl prefixl 0 []
        in ((fn s => insert AV (s,BODY)),         (* insertAVbody *)
            (fn (s,i) => insert AV (s,PREFIX i)), (* insertAVprefix *)
            peek AV,                              (* lookAV *)
            dupls)
        end
     fun variantAV n =
       let val next = Lexis.tyvar_vary
           fun loop s = case lookAV s of NONE => s | SOME _ => loop (next s)
       in loop n
       end
     fun CVs (TyFv(n,_,_)) capt k =
          (case lookAV n
            of SOME (PREFIX i) => k (add_vi capt (vmap i,i))
             | SOME BODY => k capt
             | NONE => (insertAVbody n; k capt))
       | CVs(TyApp(opr,ty)) capt k = CVs opr capt (fn c => CVs ty c k)
       | CVs(TyAll(_,M)) capt k  = CVs M capt k
       | CVs(TyAbs(_,M)) capt k  = CVs M capt k
       | CVs t capt k = k capt
     fun unclash insert [] = ()
       | unclash insert ((v,i)::rst) =
           let val (n,arity,rank) = (* dest_var *) v
               val n' = variantAV n
               val v' = (* mk_var *) (n',arity,rank)
           in Array.update(prefix,i,v')
            ; insert (n',i)
            ; unclash insert rst
           end
     fun unbind (v as TyBv i) j k =
                 k (TyFv (vmap(i-j)) handle Subscript => v)
       | unbind (TyApp(opr,ty)) j k = unbind opr j (fn opr' =>
                                      unbind ty  j (fn ty' =>
                                        k (TyApp(opr',ty'))))
       | unbind (TyAll(v,B)) j k  = unbind B (j+1) (fn q => k(TyAll(v,q)))
       | unbind (TyAbs(v,B)) j k  = unbind B (j+1) (fn q => k(TyAbs(v,q)))
       | unbind t j k = k t
 in
     unclash insertAVprefix (List.rev dupls)
   ; unclash (insertAVbody o fst) (HOLset.listItems(CVs body vi_empty I))
   ; (List.map TyFv (array_to_revlist prefix), unbind body 0 I)
 end
 end
end;

val strip_univ_type = strip_univ_binder NONE;

local exception CLASH
in
fun dest_univ_type(TyAll(Bvar as (Name,_,_), Body)) =
    let fun dest ((v as TyBv j), i) = if i=j then TyFv Bvar else v
          | dest ((v as TyFv(s,_,_)), i) =
                 if Name=s then raise CLASH else v
          | dest (TyApp(opr, ty), i)    = TyApp(dest(opr,i), dest(ty,i))
          | dest (TyAll(Bvar,Body),i)   = TyAll(Bvar, dest(Body,i+1))
          | dest (TyAbs(Bvar,Body),i)   = TyAbs(Bvar, dest(Body,i+1))
          | dest (ty,_) = ty
    in (TyFv Bvar, dest(Body,0))
       handle CLASH =>
              dest_univ_type(TyAll(variant_tyvar (type_vars Body) Bvar, Body))
    end
  | dest_univ_type _ = raise ERR "dest_univ_type" "not a universal type"
end;

fun break_univ_type(TyAll(_,Body)) = Body
  | break_univ_type _ = raise ERR "break_univ_type" "not a universal type";


(* Now for type abstractions. *)

local fun peel f ty A =
            case f ty of
              SOME(TyAbs(v,M)) => peel f M (v::A)
            | otherwise => (A,ty)
      datatype occtype = PREFIX of int | BODY
      fun array_to_revlist A =
        let val top = Array.length A - 1
            fun For i B = if i>top then B else For (i+1) (Array.sub(A,i)::B)
        in For 0 []
        end
      val vi_empty = HOLset.empty (fn ((v1,i1),(v2,i2)) => tyvar_compare(v1,v2))
      fun add_vi viset vi =
         if HOLset.member(viset,vi) then viset else HOLset.add(viset,vi)
in
fun strip_abs_binder opt =
 let val f =
         case opt of
           NONE => (fn (t as TyAbs _) => SOME t
                     | other => NONE)
         | SOME c => (fn t => let val (name,args) = dest_type t
                              in if name = c
                                 then SOME (mk_type(name, args))
                                 else NONE
                              end handle HOL_ERR _ => NONE)
 in fn ty =>
   let val (prefixl,body) = peel f ty []
     val prefix = Array.fromList prefixl
     val vmap = curry Array.sub prefix
     val (insertAVbody,insertAVprefix,lookAV,dupls) =
        let open Polyhash  (* AV is hashtable  of (var,occtype) elems *)
            val AV = mkPolyTable(Array.length prefix, Fail"AV")
            fun insertl [] _ dupls = dupls
              | insertl (x::rst) i dupls =
                  let val n =  #1 x (* fst(dest_var x) *)
                  in case peekInsert AV (n,PREFIX i)
                      of NONE => insertl rst (i+1) dupls
                       | SOME _ => insertl rst (i+1) ((x,i)::dupls)
                  end
            val dupls = insertl prefixl 0 []
        in ((fn s => insert AV (s,BODY)),         (* insertAVbody *)
            (fn (s,i) => insert AV (s,PREFIX i)), (* insertAVprefix *)
            peek AV,                              (* lookAV *)
            dupls)
        end
     fun variantAV n =
       let val next = Lexis.tyvar_vary
           fun loop s = case lookAV s of NONE => s | SOME _ => loop (next s)
       in loop n
       end
     fun CVs (TyFv(n,_,_)) capt k =
          (case lookAV n
            of SOME (PREFIX i) => k (add_vi capt (vmap i,i))
             | SOME BODY => k capt
             | NONE => (insertAVbody n; k capt))
       | CVs(TyApp(opr,ty)) capt k = CVs opr capt (fn c => CVs ty c k)
       | CVs(TyAll(_,M)) capt k  = CVs M capt k
       | CVs(TyAbs(_,M)) capt k  = CVs M capt k
       | CVs t capt k = k capt
     fun unclash insert [] = ()
       | unclash insert ((v,i)::rst) =
           let val (n,arity,rank) = (* dest_var *) v
               val n' = variantAV n
               val v' = (* mk_var *) (n',arity,rank)
           in Array.update(prefix,i,v')
            ; insert (n',i)
            ; unclash insert rst
           end
     fun unbind (v as TyBv i) j k =
                 k (TyFv (vmap(i-j)) handle Subscript => v)
       | unbind (TyApp(opr,ty)) j k = unbind opr j (fn opr' =>
                                      unbind ty  j (fn ty' =>
                                        k (TyApp(opr',ty'))))
       | unbind (TyAll(v,B)) j k  = unbind B (j+1) (fn q => k(TyAll(v,q)))
       | unbind (TyAbs(v,B)) j k  = unbind B (j+1) (fn q => k(TyAbs(v,q)))
       | unbind t j k = k t
 in
     unclash insertAVprefix (List.rev dupls)
   ; unclash (insertAVbody o fst) (HOLset.listItems(CVs body vi_empty I))
   ; (List.map TyFv (array_to_revlist prefix), unbind body 0 I)
 end
 end
end;

val strip_abs_type = strip_abs_binder NONE;

local exception CLASH
in
fun dest_abs_type(TyAbs(Bvar as (Name,_,_), Body)) =
    let fun dest ((v as TyBv j), i) = if i=j then TyFv Bvar else v
          | dest ((v as TyFv(s,_,_)), i) =
                 if Name=s then raise CLASH else v
          | dest (TyApp(opr, ty), i)    = TyApp(dest(opr,i), dest(ty,i))
          | dest (TyAll(Bvar,Body),i)   = TyAll(Bvar, dest(Body,i+1))
          | dest (TyAbs(Bvar,Body),i)   = TyAbs(Bvar, dest(Body,i+1))
          | dest (ty,_) = ty
    in (TyFv Bvar, dest(Body,0))
       handle CLASH =>
              dest_abs_type(TyAbs(variant_tyvar (type_vars Body) Bvar, Body))
    end
  | dest_abs_type _ = raise ERR "dest_abs_type" "not a type abstraction"
end;

fun break_abs_type(TyAbs(_,Body)) = Body
  | break_abs_type _ = raise ERR "break_abs_type" "not a type abstraction";


(*---------------------------------------------------------------------------
    Does there exist a free type variable v in a type such that P(v) holds.
    Returns false if there are no free type variables in the type.
 ---------------------------------------------------------------------------*)

fun exists_tyvar P =
 let fun occ (w as TyFv _) = P w
       | occ (TyApp(Opr,Arg)) = occ Opr orelse occ Arg
       | occ (TyAll(_,ty)) = occ ty
       | occ (TyAbs(_,ty)) = occ ty
       | occ ty = false
 in occ end;

(*---------------------------------------------------------------------------
     Does a type variable occur free in a type
 ---------------------------------------------------------------------------*)

fun type_var_in v =
  if is_vartype v then exists_tyvar (type_eq v)
                  else raise ERR "type_var_occurs" "not a type variable"

(*
(*---------------------------------------------------------------------------*
 * Substitute in a type, trying to preserve existing structure.              *
 * Doesn't work for universal types and type abstractions.  Obsolete.        *
 *---------------------------------------------------------------------------*)

fun ty_sub [] _ = SAME
  | ty_sub theta (TyCon tyc) = SAME
  | ty_sub theta (TyApp (Opr,Ty))
      = (case delta_pair (ty_sub theta) (ty_sub theta) (Opr,Ty)
          of SAME => SAME
           | DIFF (Opr',Ty') => DIFF (TyApp(Opr', Ty'))
  | ty_sub theta (TyAll (a,Body))
      = (case ty_sub theta Body
          of SAME => SAME
           | DIFF Body' => DIFF (TyAll(tyc, Args')))
  | ty_sub theta v =
      case Lib.subst_assoc (type_eq v) theta
       of NONE    => SAME
        | SOME ty => DIFF ty

fun type_subst theta = delta_apply (ty_sub theta)
*)


(*---------------------------------------------------------------------------*
 *    Replace arbitrary subtypes in a type. Non-renaming.                    *
 *---------------------------------------------------------------------------*)

fun subst_rank [] = 0
  | subst_rank ({redex,residue} :: s) =
      let val rk_dex = rank_of redex
          val rk_due = rank_of residue
      in
         Int.max( if rk_dex >= rk_due then 0
                  else rk_due - rk_dex,
                  subst_rank s )
      end

fun inst_rank_subst r [] = []
  | inst_rank_subst r ({redex,residue} :: s) =
      ({redex=inst_rank r redex, residue=residue} :: inst_rank_subst r s)

val emptysubst:(hol_type,hol_type)Binarymap.dict = Binarymap.mkDict compare
local
  open Binarymap
  fun addb [] A = A
    | addb ({redex,residue}::t) (A,b) =
        if (kind_of redex <> kind_of residue) handle HOL_ERR _ => false
           (* if "kind_of" fails because of open bound variables,
              assume the kind check was done earlier and proceed. *)
        then raise ERR "type_subst" "redex has different kind than residue"
        else if (rank_of redex < rank_of residue) handle HOL_ERR _ => false
           (* if "rank_of" fails because of open bound variables,
              assume the rank check was done earlier and proceed. *)
        then raise ERR "type_subst" "type substitution does not respect rank"
        else addb t (insert(A,redex,residue),
                     is_vartype redex andalso b)
in
fun raw_type_subst [] = I
  | raw_type_subst theta =
    let val (fmap,b) = addb theta (emptysubst, true)
        fun vsubs (v as TyFv _) =
               (case peek(fmap,v) of NONE => v
                                   | SOME y => y)
          | vsubs (TyApp(opr,ty)) = TyApp(vsubs opr, vsubs ty)
          | vsubs (TyAll(Bvar,Body)) = TyAll(Bvar,vsubs Body)
          | vsubs (TyAbs(Bvar,Body)) = TyAbs(Bvar,vsubs Body)
          | vsubs t = t
        fun subs ty =
          case peek(fmap,ty)
           of SOME residue => residue
            | NONE =>
              (case ty
                of TyApp(opr,ty) => TyApp(subs opr, subs ty)
                 | TyAll(Bvar,Body) => TyAll(Bvar,subs Body)
                 | TyAbs(Bvar,Body) => TyAbs(Bvar,subs Body)
                 | _ => ty)
    in
      (if b then vsubs else subs)
    end

fun type_subst s =
   let val r = subst_rank s
   in if r = 0 then raw_type_subst s
      else let val s' = inst_rank_subst r s
           in raw_type_subst s' o inst_rank r
           end
   end

end;

fun ty_sub theta ty = let val ty' = type_subst theta ty
                      in if type_eq ty ty' then SAME
                                           else DIFF ty'
                      end;

local
  open Binarymap
in
fun type_map fmap =
    let 
        fun subs ty =
          case peek(fmap,ty)
           of SOME residue => residue
            | NONE =>
              (case ty
                of TyApp(opr,ty) => TyApp(subs opr, subs ty)
                 | TyAll(Bvar,Body) => TyAll(Bvar,subs Body)
                 | TyAbs(Bvar,Body) => TyAbs(Bvar,subs Body)
                 | _ => ty)
    in subs
    end
end;

(*---------------------------------------------------------------------------*
 * Is a type polymorphic, or contain a universal type or type abstraction?   *
 *---------------------------------------------------------------------------*)

fun polymorphic (TyFv _)          = true
  | polymorphic (TyBv _)          = true
  | polymorphic (TyApp (Opr,Arg)) = polymorphic Opr orelse polymorphic Arg
  | polymorphic (TyAll (_,Body))  = polymorphic Body
  | polymorphic (TyAbs (_,Body))  = polymorphic Body
  | polymorphic _                 = false

fun universal (TyAll _)         = true
  | universal (TyApp (Opr,Arg)) = universal Opr orelse universal Arg
  | universal (TyAbs (_,Body))  = universal Body
  | universal _                 = false

fun abstraction (TyAbs _)         = true
  | abstraction (TyApp (Opr,Arg)) = abstraction Opr orelse abstraction Arg
  | abstraction (TyAll (_,Body))  = abstraction Body
  | abstraction _                 = false

(*--------------------------------------------------------------------------------
    Matching (first order, modulo alpha conversion) of types, including
    sets of type variables to avoid binding.
    Now replaced by higher order matching of types, modulo alpha-beta conversion.
 --------------------------------------------------------------------------------*)

local
  fun MERR s = raise ERR "raw_match_type error" s
  fun free (TyBv i) n         = i<n
    | free (TyApp(Opr,Arg)) n = free Opr n andalso free Arg n
    | free (TyAll(_,Body)) n  = free Body (n+1)
    | free (TyAbs(_,Body)) n  = free Body (n+1)
    | free _ _                = true
  fun lookup eq x ids =
   let fun look [] = if HOLset.member(ids,x) then SOME x else NONE
         | look ({redex,residue}::t) =
              if eq x redex then SOME residue else look t
   in look end
  fun bound_by_scope scoped M = if scoped then not (free M 0) else false
  fun tasks (ty1::tys1) (ty2::tys2) s rst = (ty1,ty2,s)::tasks tys1 tys2 s rst
    | tasks [] [] s rst = rst
    | tasks _ _ _ _ = MERR "different arities of type operators"
in
fun RM [] theta = theta
  | RM (((v as TyFv(_,kd,rk)),ty,scoped)::rst) (S1 as (tyS,Id))
     = if bound_by_scope scoped ty
       then MERR "type variable bound by scope"
       else if kd <> kind_of ty
       then MERR "type variable has different kind"
       else RM rst
             (case lookup equal v Id tyS
               of NONE => if type_eq v ty then (tyS,HOLset.add(Id,v))
                                  else ((v |-> ty)::tyS,Id)
                | SOME ty' => if aconv_ty ty' ty then S1
                              else MERR "double bind on type variable")
  | RM (((TyCon c1),(TyCon c2),s)::rst) tyS
      = if c1 = c2 then RM rst tyS
        else let val n1 = KernelSig.id_toString (#1 c1)
                 val n2 = KernelSig.id_toString (#1 c2)
             in MERR ("attempt to match different type constants: "
                      ^n1^" against "^n2)
             end
  | RM ((TyApp(op1,ty1),TyApp(op2,ty2),s)::rst) tyS
      = RM (tasks [op1,ty1] [op2,ty2] s rst) tyS
  | RM ((TyAll((p as (_,a1,rk1)),M),TyAll((q as (_,a2,rk2)),N),_)::rst) tyS
      = if (a1 <> a2) orelse (rk1 < rk2)
        then MERR "different universal type quantifications"
        else RM ((M,N,true)::rst) tyS
  | RM ((TyAbs((p as (_,a1,rk1)),M),TyAbs((q as (_,a2,rk2)),N),_)::rst) tyS
      = if (a1 <> a2) orelse (rk1 < rk2)
        then MERR "different universal type quantifications"
        else RM ((M,N,true)::rst) tyS
  | RM ((TyBv i,TyBv j,s)::rst) S
      = if i=j then RM rst S
               else MERR "Bound variable depth"
  | RM all others                      = MERR "different constructors"
end

fun raw_match_type pat ob (tyS,tyfixed) =
    let val tyfixed_set = HOLset.addList(empty_tyset, tyfixed)
        val (tyS',Id) =
              RM [(pat,ob,false)] (tyS,tyfixed_set)
        val Id' = HOLset.listItems Id
     in (tyS',Id')
    end;

fun match_type_restr fixed pat ob  = fst (raw_match_type pat ob ([],fixed))
fun match_type_in_context pat ob S = fst (raw_match_type pat ob (S,[]))

fun match_type pat ob = fst (raw_match_type pat ob ([],[]))

fun beta_conv_ty (TyApp(M as TyAbs _, N))
       = let val (btyv,body) = dest_abs_type M
         in type_subst [btyv |-> N] body
         end
  | beta_conv_ty _ = raise ERR "beta_conv_ty" "not a type beta redex"

exception UNCHANGEDTY;

fun qconv_ty c ty = c ty handle UNCHANGEDTY => ty

(* ---------------------------------------------------------------------*)
(* rand_conv_ty conv ``:t2 t1`` applies conv to t2                      *)
(* ---------------------------------------------------------------------*)

fun rand_conv_ty conv ty = let
  val (Rator,Rand) =
    dest_app_type ty handle HOL_ERR e => raise ERR "rand_conv_ty" "not a type app"
  val Newrand = conv Rand
    handle HOL_ERR {origin_function, message, origin_structure} =>
      if Lib.mem origin_function
           ["rand_conv_ty", "rator_conv_ty", "abs_conv_ty", "univ_conv_ty"]
         andalso origin_structure = "Type"
      then
        raise ERR "rand_conv_ty" message
      else
        raise ERR "rand_conv_ty" (origin_function ^ ": " ^ message)
in
  mk_app_type(Rator, Newrand) handle (HOL_ERR {message,...}) =>
    raise ERR "rand_conv_ty" ("Application of mk_app_type failed: "^message)
end

(* ---------------------------------------------------------------------*)
(* rator_conv_ty conv ``:t2 t1`` applies conv to t1                     *)
(* ---------------------------------------------------------------------*)

fun rator_conv_ty conv ty = let
  val (Rator,Rand) =
    dest_app_type ty handle HOL_ERR e => raise ERR "rator_conv_ty" "not a type app"
  val Newrator = conv Rator
    handle HOL_ERR {origin_function, message, origin_structure} =>
      if Lib.mem origin_function
           ["rand_conv_ty", "rator_conv_ty", "abs_conv_ty", "univ_conv_ty"]
         andalso origin_structure = "Type"
      then
        raise ERR "rator_conv_ty" message
      else
        raise ERR "rator_conv_ty" (origin_function ^ ": " ^ message)
in
  mk_app_type(Newrator, Rand) handle (HOL_ERR {message,...}) =>
    raise ERR "rator_conv_ty" ("Application of mk_app_type failed: "^message)
end

(* ----------------------------------------------------------------------
    abs_conv_ty conv ``: \'a. t['a]`` applies conv to t['a]
   ---------------------------------------------------------------------- *)

fun abs_conv_ty conv ty = let
  val (Bvar,Body) =
    dest_abs_type ty handle HOL_ERR e => raise ERR "abs_conv_ty" "not a type abstraction"
  val Newbody = conv Body
    handle HOL_ERR {origin_function, message, origin_structure} =>
      if Lib.mem origin_function
           ["rand_conv_ty", "rator_conv_ty", "abs_conv_ty", "univ_conv_ty"]
         andalso origin_structure = "Type"
      then
        raise ERR "abs_conv_ty" message
      else
        raise ERR "abs_conv_ty" (origin_function ^ ": " ^ message)
in
  mk_abs_type(Bvar, Newbody) handle (HOL_ERR {message,...}) =>
    raise ERR "abs_conv_ty" ("Application of mk_abs_type failed: "^message)
end

(* ----------------------------------------------------------------------
    univ_conv_ty conv ``: !'a. t['a]`` applies conv to t['a]
   ---------------------------------------------------------------------- *)

fun univ_conv_ty conv ty = let
  val (Bvar,Body) =
    dest_univ_type ty handle HOL_ERR e => raise ERR "univ_conv_ty" "not a universal type"
  val Newbody = conv Body
    handle HOL_ERR {origin_function, message, origin_structure} =>
      if Lib.mem origin_function
           ["rand_conv_ty", "rator_conv_ty", "abs_conv_ty", "univ_conv_ty"]
         andalso origin_structure = "Type"
      then
        raise ERR "univ_conv_ty" message
      else
        raise ERR "univ_conv_ty" (origin_function ^ ": " ^ message)
in
  mk_univ_type(Bvar, Newbody) handle (HOL_ERR {message,...}) =>
    raise ERR "univ_conv_ty" ("Application of mk_univ_type failed: "^message)
end

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
   in if aconv_ty ty ty1 then raise ERR"changed_conv_ty" "Input type unchanged"
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
    try_conv_ty (app_conv_ty conv orelse_ty abs_conv_ty conv orelse_ty univ_conv_ty conv)

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


fun abconv_ty t1 t2 = aconv_ty (deep_beta_conv_ty t1) (deep_beta_conv_ty t2)


(*---------------------------------------------------------------------------
       Higher order matching (from jrh via Michael Norrish - June 2001)
       Adapted to HOL-Omega types by PVH - July 18, 2008
 ---------------------------------------------------------------------------*)

local
  fun MERR s = raise ERR "raw_match_type error" s
  exception NOT_FOUND
  val abconv_ty = aconv_ty (* do beta-reduction first before entering these functions *)
  fun find_residue_ty red [] = raise NOT_FOUND
    | find_residue_ty red ({redex,residue}::rest) = if abconv_ty red redex then residue
                                                    else find_residue_ty red rest
  fun in_dom x [] = false
    | in_dom x ({redex,residue}::rest) = (x = redex) orelse in_dom x rest
  fun safe_insert_ty (n as {redex,residue}) l = let
    val z = find_residue_ty redex l
  in
    if residue = z then l
    else raise ERR "safe_insert_ty" "match"
  end handle NOT_FOUND => n::l
  fun safe_insert_tya (n as {redex,residue}) l = let
    val z = find_residue_ty redex l
  in
    if abconv_ty residue z then l
    else raise ERR "safe_insert_tya" "match"
  end handle NOT_FOUND => n::l
  val mk_dummy_ty = let
    val name = dest_vartype(gen_tyvar())
  in fn (kd,rk) => with_flag (varcomplain,false) mk_vartype_opr(name, kd, rk)
  end
  fun rator_type ty = fst (dest_app_type ty)


  fun type_pmatch lconsts env (TyBv i) (TyBv j) (sofar as (insts,homs))
      = if i=j then sofar
        else MERR "bound type variable mismatch"
    | type_pmatch lconsts env (TyBv _) _ (sofar as (insts,homs))
      = MERR "bound type variable mismatch"
    | type_pmatch lconsts env _ (TyBv _) (sofar as (insts,homs))
      = MERR "bound type variable mismatch"
    | type_pmatch lconsts env vty cty (sofar as (insts,homs)) =
    if is_vartype vty then let
        val cty' = find_residue_ty vty env
      in
        if aconv_ty cty' cty then sofar else MERR "type variable mismatch"
      end handle NOT_FOUND =>
                 if HOLset.member(lconsts, vty) then
                   if abconv_ty cty vty then sofar
                   else MERR "can't instantiate local constant"
                 else (safe_insert_tya (vty |-> cty) insts, homs)
               | HOL_ERR _ => MERR "free type variable mismatch"
    else if is_con_type vty then let
        val {Thy = vthy, Tyop = vname, Kind = vkd, Rank = vrk} = dest_thy_con_type vty
        val {Thy = cthy, Tyop = cname, Kind = ckd, Rank = crk} = dest_thy_con_type cty
                handle HOL_ERR _ => MERR "type constant mismatched with non-constant"
      in
        if vname = cname andalso vthy = cthy then
          if ckd = vkd andalso crk = vrk then sofar
          else (safe_insert_tya (mk_dummy_ty(vkd,vrk) |-> mk_dummy_ty(ckd,crk)) insts, homs)
        else MERR "type constant mismatch"
      end
    else if is_abs_type vty then let
        val (vv,vbod) = dest_abs_type vty
        val (cv,cbod) = dest_abs_type cty
                handle HOL_ERR _ => MERR "abstraction type mismatched with non-abstraction type"
        val (_, vkd, vrk) = dest_vartype_opr vv
        val (_, ckd, crk) = dest_vartype_opr cv
        val sofar' = (safe_insert_tya (mk_dummy_ty(vkd,vrk) |-> mk_dummy_ty(ckd,crk)) insts, homs)
      in
        type_pmatch lconsts ((vv |-> cv)::env) vbod cbod sofar'
      end
    else if is_univ_type vty then let
        val (vv,vbod) = dest_univ_type vty
        val (cv,cbod) = dest_univ_type cty
                handle HOL_ERR _ => MERR "universal type mismatched with non-universal type"
        val (_, vkd, vrk) = dest_vartype_opr vv
        val (_, ckd, crk) = dest_vartype_opr cv
        val sofar' = (safe_insert_tya (mk_dummy_ty(vkd,vrk) |-> mk_dummy_ty(ckd,crk)) insts, homs)
      in
        type_pmatch lconsts ((vv |-> cv)::env) vbod cbod sofar'
      end
    else (* is_app_type *) let
        val vhop = repeat rator_type vty
      in
        if is_vartype vhop andalso not (HOLset.member(lconsts, vhop)) andalso
           not (in_dom vhop env)
        then let (* kind_of and rank_of can fail if given an open type with free bound variables, as cty might be *)
            val vkd = kind_of vty
            val vrk = rank_of vty
            val ckd = kind_of cty
            val crk = rank_of cty
            val insts' = if vkd = ckd andalso vrk = crk then insts
                         else safe_insert_tya (mk_dummy_ty(vkd,vrk) |-> mk_dummy_ty(ckd,crk)) insts
          in
            (insts', (env,cty,vty)::homs)
          end
        else let
            val (lv,rv) = dest_app_type vty
            val (lc,rc) = dest_app_type cty
                handle HOL_ERR _ => MERR "application type mismatched with non-application type"
            val sofar' = type_pmatch lconsts env lv lc sofar
          in
            type_pmatch lconsts env rv rc sofar'
          end
      end


fun separate_insts_ty (insts :{redex : hol_type, residue : hol_type} list) = let
  val (realinsts, patterns) = partition (is_vartype o #redex) insts
  val betacounts =
      if patterns = [] then []
      else
        itlist (fn {redex = p,...} =>
                   fn sof => let
                        val (hop,args) = strip_app_type p
                      in
                        safe_insert_ty (hop |-> length args) sof
                      end handle _ =>
                                 (HOL_WARNING "" ""
                                  "Inconsistent patterning in h.o. type match";
                                  sof))
        patterns []
in
  (betacounts,
   mapfilter (fn {redex = x, residue = t} =>
                   if t = x then raise ERR "separate_insts_ty" ""
                            else {redex = x, residue = t}
             ) realinsts
  )
end


fun all_abconv [] [] = true
  | all_abconv [] _ = false
  | all_abconv _ [] = false
  | all_abconv (h1::t1) (h2::t2) = abconv_ty h1 h2 andalso all_abconv t1 t2


fun type_homatch lconsts (insts, homs) = let
  (* local constants of types never change *)
  val type_homatch = type_homatch lconsts
in
  if homs = [] then insts
  else let
      val (env,cty,vty) = hd homs
    in
      if is_vartype vty then
        if aconv_ty cty vty then type_homatch (insts, tl homs)
        else let
            val newinsts = (vty |-> cty)::insts
          in
            type_homatch (newinsts, tl homs)
          end
      else (* vty not a type var *) let
          val (vhop, vargs) = strip_app_type vty
          val afvs = type_varsl vargs
          (*val inst_fn = Type.inst (fst tyins)*)
        in
          (let
             val tyins =
                 map (fn a =>
                         ((*inst_fn*) a |->
                                  (find_residue_ty a env
                                   handle _ =>
                                          find_residue_ty a insts
                                   handle _ =>
                                          if HOLset.member(lconsts, a)
                                          then a
                                          else raise ERR "type_homatch" ""))) afvs
             val pats0 = (*map inst_fn*) vargs
             val pats = map (type_subst tyins) pats0
             val vhop' = (*inst_fn*) vhop
             val icty = list_mk_app_type(vhop', pats)
             val ni = let
               val (chop,cargs) = strip_app_type cty
             in
               if all_abconv cargs pats then
                 if abconv_ty chop vhop then insts
                 else safe_insert_tya (vhop |-> chop) insts
               else let
                   val ginsts = map (fn p => (p |->
                                                (if is_vartype p then p
                                                 else gen_tyopvar(kind_of p,rank_of p))))
                                    pats
                   val cty' = type_subst ginsts cty
                   val gvs = map #residue ginsts
                   val absty = list_mk_abs_type(gvs,cty')
                   val vinsts = safe_insert_tya (vhop |-> absty) insts
                   val icpair = (list_mk_app_type(vhop',gvs) |-> cty')
                 in
                   icpair::vinsts
                 end
             end
           in
             type_homatch (ni,tl homs)
           end) handle _ => let
                         val (lc,rc) = dest_app_type cty
                         val (lv,rv) = dest_app_type vty
                         val pinsts_homs' =
                             type_pmatch lconsts env rv rc
                                         (insts, (env,lc,lv)::(tl homs))
                       in
                         type_homatch pinsts_homs'
                       end
        end
    end
end

in

val type_pmatch = type_pmatch
val separate_insts_ty = separate_insts_ty
val all_abconv = all_abconv
val type_homatch = type_homatch

fun ho_match_type1 lconsts vty cty insts_homs = let
  val pinsts_homs = type_pmatch lconsts [] vty cty insts_homs
  val insts = type_homatch lconsts pinsts_homs
in
  separate_insts_ty insts
end

fun ho_match_type0 lconsts vty cty =
    ho_match_type1 lconsts vty cty ([], [])

fun ho_match_type lconsts vty cty = let
  val (bcs, tyins) = ho_match_type0 lconsts vty cty
in
  tyins
end handle e => raise (wrap_exn "HolKernel" "ho_match_type" e)

(*
val s0 = HOLset.empty Type.compare;
val s1 = HOLset.add(s0,alpha);
ho_match_type s1 ``:'a 'b`` ``:('a -> 'a) # 'c``;
> val it = [{redex = ``:'b``, residue = ``:\'a. ('a -> 'a) # 'c``}] :
  {redex : hol_type, residue : hol_type} list
ho_match_type s0 ``:'a + 'b`` ``:('a -> 'a) # 'c`` handle e => Raise e;
ho_match_type s1 ``:'a 'b`` ``:('a -> 'b) # 'a``;
ho_match_type s0 ``:'a # 'b`` ``:('a -> 'b) # 'a`` handle e => Raise e;
ho_match_type s0 ``:('a -> 'b) # 'b`` ``:'a # 'b`` handle e => Raise e;
*)

end (* local *)

(* We redefine the main type matching functions here to use higher order matching. *)

fun ho_raw_match_type pat ob (tyS,tyfixed) =
    let val pat = deep_beta_conv_ty pat
        val ob  = deep_beta_conv_ty ob
        fun beta_conv_S {redex,residue} =
            {redex=redex, residue = deep_beta_conv_ty residue}
        val tyS = map beta_conv_S tyS
        val tyfixed_set = HOLset.addList(empty_tyset, tyfixed)
        val (_,tyS') = ho_match_type1 tyfixed_set pat ob (tyS,[])
        val Id = Lib.subtract (Lib.union (type_vars pat) tyfixed) (map #redex tyS')
     in (tyS',Id)
    end;

val raw_match_type = ho_raw_match_type

fun match_type_restr fixed pat ob  = fst (ho_raw_match_type pat ob ([],fixed))
fun match_type_in_context pat ob S = fst (ho_raw_match_type pat ob (S,[]))

fun match_type pat ob = fst (ho_raw_match_type pat ob ([],[]))


(*---------------------------------------------------------------------------
   Full propagation of substitutions. (unnecessary if no type substitutions)
 ---------------------------------------------------------------------------*)

local
  fun tyvars_sigma_norm (s,ty) =
    case ty of
      TyFv _ => ty
    | TyBv i =>
        (case Subst.exp_rel(s,i) of
           (0, SOME v)   => tyvars_sigma_norm (Subst.id, v)
         | (lams,SOME v) => tyvars_sigma_norm (Subst.shift(lams,Subst.id),v)
         | (lams,NONE)   => TyBv lams)
    | TyApp(Opr,Ty) => TyApp(tyvars_sigma_norm(s, Opr),
                             tyvars_sigma_norm(s, Ty ))
    | TyAll(Btyvar,Body) => TyAll(Btyvar, tyvars_sigma_norm (Subst.lift(1,s),
                                                             Body))
    | TyAbs(Btyvar,Body) => TyAbs(Btyvar, tyvars_sigma_norm (Subst.lift(1,s),
                                                             Body))
    | _ => ty  (* i.e., a const *)
in
fun norm_clos ty = tyvars_sigma_norm(Subst.id,ty)
end


(*---------------------------------------------------------------------------*
 *       Does a type contain unbound "bound variables" (Bv's)?               *
 *---------------------------------------------------------------------------*)

local fun unb (v as TyBv i,k)    = k <= i
        | unb (TyApp(opr,arg),k) = unb(opr,k) orelse unb(arg,k)
        | unb (TyAll(bv,Body),k) = unb(Body,k+1)
        | unb (TyAbs(bv,Body),k) = unb(Body,k+1)
        | unb (_,_) = false (* e.g., free type variables, constants *)
in
fun unbound_ty ty = unb(ty,0)
end;


(*---------------------------------------------------------------------------*
 *  Raw syntax prettyprinter for types.                                      *
 *---------------------------------------------------------------------------*)

val dot     = "."
val dollar  = "$"
val percent = "%";

fun pp_raw_type pps ty =
 let open Portable
     val {add_string,add_break,begin_block,end_block,...} = with_ppstream pps
     val pp_kind = Kind.pp_kind pps
     fun pp_kind_rank (kind,rank) =
          ( if kind = typ then ()
            else (add_string "::"; pp_kind kind);
            if rank = 0 then ()
            else add_string ("/"^Lib.int_to_string rank) )
     fun pp (TyAbs(Btyvar,Body)) =
          ( add_string "(\\:";
            pp (TyFv Btyvar); add_string dot; add_break(1,0);
            pp Body; add_string ")" )
      | pp (TyAll(Btyvar,Body)) =
          ( add_string "(!:";
            pp (TyFv Btyvar); add_string dot; add_break(1,0);
            pp Body; add_string ")" )
      | pp (TyApp(Rator as TyApp(TyCon(id,_,_),Rand1),Rand2)) =
          if KernelSig.name_of id = "fun"
          then
          ( add_string "("; pp Rand2;
            add_string " ->"; add_break(1,0);
            pp Rand1; add_string ")" )
          else
          ( add_string "("; pp Rand2; add_break(1,0);
                            pp Rator; add_string ")")
      | pp (ty as TyApp(Rator,Rand)) =
          let val (c,args) = strip_app_type ty
          in if length args = 1 then
          ( add_string "("; pp Rand; add_break(1,0);
                            pp Rator; add_string ")")
             else
          ( add_string "(("; pps args; add_string ")";
            add_break(1,0); pp c; add_string ")" )
          end
      | pp (TyBv i) = add_string (dollar^Lib.int_to_string i)
      | pp (TyFv (name,kind,rank)) =
         ( add_string name;
           pp_kind_rank (kind,rank) )
      | pp (TyCon (id,kind,rank)) =
         ( add_string ( (* seg_of id^dollar^ *) KernelSig.name_of id);
           pp_kind_rank (kind,rank) )
    and pps [] = ()
      | pps [ty] = pp ty
      | pps (ty :: tys) = (pp ty; add_string ",";
                           add_break(0,0); pps tys)
 in
   begin_block INCONSISTENT 0;
   add_string "`:";
   pp (norm_clos ty);
   add_string "`";
   end_block()
 end;

(*---------------------------------------------------------------------------*)
(* Send the results of prettyprinting to a string                            *)
(*---------------------------------------------------------------------------*)

fun sprint pp x = PP.pp_to_string 72 pp x

val type_to_string = sprint pp_raw_type;

(*
val _ = installPP Kind.pp_kind;
val _ = installPP pp_raw_type;
*)


end (* Type *)
