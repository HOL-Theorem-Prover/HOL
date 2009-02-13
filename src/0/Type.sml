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

quotation := true;
loadPath := "/Users/palantir" ^ "/hol/hol-omega/sigobj" :: !loadPath;

quotation := true;
loadPath := "/Users/pvhomei" ^ "/hol/hol-omega/sigobj" :: !loadPath;

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

(*---------------------------------------------------------------------------
        Some basic values
 ---------------------------------------------------------------------------*)

val bool = TyCon bool_tyc
val ind  = TyCon ind_tyc;


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


(*---------------------------------------------------------------------------*
 * Computing the kind of a type, assuming it is well-kinded.                 *
 *---------------------------------------------------------------------------*)

local fun lookup 0 (kd::_)  = kd
        | lookup n (_::rst) = lookup (n-1) rst
        | lookup _ []       = raise ERR "kind_of" "lookup"
in
      fun kd_of (TyFv (_,kd,_)) _        = kd
        | kd_of (TyCon(_,kd,_)) _        = kd
        | kd_of (TyBv i) E               = lookup i E
        | kd_of (TyApp(Opr,_)) E         = snd(kind_dom_rng (kd_of Opr E))
        | kd_of (TyAll((_,Kd,_),Body)) E = kd_of Body (Kd::E)
        | kd_of (TyAbs((_,Kd,_),Body)) E = Kd ==> kd_of Body (Kd::E)
fun kind_of ty = kd_of ty []
end;

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
        | rk_of (TyAll((_,_,rk),Body)) E = max (rk + 1, rk_of Body (rk::E))
        | rk_of (TyAbs((_,_,rk),Body)) E = max (rk, rk_of Body (rk::E))
fun rank_of ty = rk_of ty []
end;

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

(*---------------------------------------------------------------------------*
 * Checking that a type is well-kinded.                                      *
 * This fn should never be needed, as long as the type constructors check.   *
 *---------------------------------------------------------------------------*)

fun is_well_kinded ty = (check_kind_of ty; true) handle HOL_ERR _ => false


(*-----------------------------------------------------------------------------*
 * The kind variables of a type. Tail recursive (from Ken Larsen).             *
 *-----------------------------------------------------------------------------*)

local fun kdV (TyFv(s,kd,rk)) k         = k (Kind.kind_vars kd)
        | kdV (TyBv _) k                = k []
        | kdV (TyCon(s,kd,rk)) k        = k (Kind.kind_vars kd)
        | kdV (TyApp(opr, arg)) k       = kdV arg (fn q1 =>
                                          kdV opr (fn q2 => k (union q2 q1)))
        | kdV (TyAll((s,kd,rk),Body)) k = kdV Body (fn q =>
                                          k (union (Kind.kind_vars kd) q))
        | kdV (TyAbs((s,kd,rk),Body)) k = kdV Body (fn q =>
                                          k (union (Kind.kind_vars kd) q))
      fun kdVs (t::ts) k                = kdV t (fn q1 =>
                                          kdVs ts (fn q2 => k (union q2 q1)))
        | kdVs [] k                     = k []
in
fun kind_vars tm = kdV tm Lib.I
fun kind_varsl tms = kdVs tms Lib.I
end;


(*---------------------------------------------------------------------------*
 * Substituting kinds for kind variables of a type.                          *
 *---------------------------------------------------------------------------*)

fun inst_kind theta =
  let val subst = Kind.kind_subst theta
      fun inst (TyFv (s,kd,rk))        = TyFv (s,subst kd,rk)
        | inst (TyCon(s,kd,rk))        = TyCon(s,subst kd,rk)
        | inst (ty as TyBv _)          = ty
        | inst (TyApp(opr, ty))        = TyApp(inst opr, inst ty)
        | inst (TyAll((s,kd,rk),Body)) = TyAll((s,subst kd,rk), inst Body)
        | inst (TyAbs((s,kd,rk),Body)) = TyAbs((s,subst kd,rk), inst Body)
  in if null theta then I
     else inst
  end;

(*---------------------------------------------------------------------------*
 * Increasing the rank of a type.                                            *
 *---------------------------------------------------------------------------*)

fun inst_rank i ty =
  let fun inc_rk (TyFv (s,kd,rk))        = TyFv (s,kd,rk+i)
        | inc_rk (TyCon(s,kd,rk))        = TyCon(s,kd,rk)
        | inc_rk (ty as TyBv _)          = ty
        | inc_rk (TyApp(opr, ty))        = TyApp(inc_rk opr,  inc_rk ty)
        | inc_rk (TyAll((s,kd,rk),Body)) = TyAll((s,kd,rk+i), inc_rk Body)
        | inc_rk (TyAbs((s,kd,rk),Body)) = TyAbs((s,kd,rk+i), inc_rk Body)
  in if i = 0 then ty
     else if i < 0 then raise ERR "inst_rank" "new rank is negative"
     else inc_rk ty
  end;


(*---------------------------------------------------------------------------*
 * Instantiating the rank variable and the kind variables of a type.         *
 * This is more efficient, as it makes a single traversal of the type.       *
 *---------------------------------------------------------------------------*)

fun inst_rank_kind rank theta =
  let val subst = Kind.kind_subst theta
      fun inst (TyFv (s,kd,rk))        = TyFv (s,subst kd,rk+rank)
        | inst (TyCon(s,kd,rk))        = TyCon(s,subst kd,rk)
        | inst (ty as TyBv _)          = ty
        | inst (TyApp(opr, ty))        = TyApp(inst opr, inst ty)
        | inst (TyAll((s,kd,rk),Body)) = TyAll((s,subst kd,rk+rank), inst Body)
        | inst (TyAbs((s,kd,rk),Body)) = TyAbs((s,subst kd,rk+rank), inst Body)
  in if rank < 0 then raise ERR "inst_rank_kind" "new rank is negative"
     else if rank = 0 then inst_kind theta
     else if null theta then inst_rank rank
     else inst
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
        | TV (TyAll(v,ty)) A k    = TV ty A k
        | TV (TyAbs(v,ty)) A k    = TV ty A k
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

fun tyvar_subtype ((s1,k1,rk1), (s2,k2,rk2)) =
       (s1 = s2) andalso (k1 = k2) andalso (rk1 <= rk2)

val empty_tyvarset = HOLset.empty tyvar_compare
fun tyvar_eq t1 t2 = tyvar_compare(t1,t2) = EQUAL;

fun type_var_compare (TyFv u, TyFv v) = tyvar_compare (u,v)
  | type_var_compare _ =raise ERR "type_var_compare" "variables required";

fun type_var_subtype (TyFv u, TyFv v) = tyvar_subtype (u,v)
  | type_var_subtype _ =raise ERR "type_var_subtype" "variables required";

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

local val EQ = Portable.pointer_eq
in
fun asubtype t1 t2 = EQ(t1,t2) orelse
 case(t1,t2)
  of (u as TyFv _, v as TyFv _ ) => type_var_subtype(u,v)
   | (u as TyCon _,v as TyCon _) => type_con_compare(u,v) = EQUAL
   | (TyApp(p,t1),TyApp(q,t2)) => asubtype p q andalso asubtype t1 t2
   | (TyAll((_,k1,r1),t1),
      TyAll((_,k2,r2),t2)) => k1 = k2 andalso r1 <= r2 andalso asubtype t1 t2
   | (TyAbs((_,k1,r1),t1),
      TyAbs((_,k2,r2),t2)) => k1 = k2 andalso r1 <= r2 andalso asubtype t1 t2
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
     val prefixlen = length prefixl
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
                 k (TyFv (vmap(i-j)) handle Subscript => if i>j then TyBv(i-prefixlen) (* new! *)
                                                         else v)
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
    let fun dest ((v as TyBv j), i) = if i=j then TyFv Bvar
                                      else if i<j then TyBv (j-1) (* new! *)
                                      else v
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
     val prefixlen = length prefixl
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
                 k (TyFv (vmap(i-j)) handle Subscript => if i>j then TyBv(i-prefixlen) (* new! *)
                                                         else v)
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
    let fun dest ((v as TyBv j), i) = if i=j then TyFv Bvar
                                      else if i<j then TyBv (j-1) (* new! *)
                                      else v
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


(*---------------------------------------------------------------------------*
 *    Matching ranks, determining the necessary delta to make proper.        *
 *---------------------------------------------------------------------------*)

fun raw_match_rank pat_rk ob_rk delta =
    if pat_rk >= ob_rk then delta
    else Int.max(delta, ob_rk - pat_rk)

fun match_rank pat_rk ob_rk = raw_match_rank pat_rk ob_rk 0


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
(* NOTE: raw_type_subst must only be called with beta-reduced redexes. *)
fun raw_type_subst [] = I
  | raw_type_subst theta =
    let val (fmap,b) = addb theta (emptysubst, true)
        fun lift i j (TyBv k) = if k >= j then TyBv (i+k) else TyBv k
          | lift i j (v as TyFv _) = v
          | lift i j (c as TyCon _) = c
          | lift i j (TyApp(Opr,Arg)) = TyApp(lift i j Opr, lift i j Arg)
          | lift i j (TyAll(Bvar,Body)) = TyAll(Bvar, lift i (j+1) Body)
          | lift i j (TyAbs(Bvar,Body)) = TyAbs(Bvar, lift i (j+1) Body)
        fun vsubs i (v as TyFv _) =
               (case peek(fmap,v) of NONE => v
                                   | SOME y => lift i 0 y)
          | vsubs i (TyApp(opr,ty)) = TyApp(vsubs i opr, vsubs i ty)
          | vsubs i (TyAll(Bvar,Body)) = TyAll(Bvar,vsubs (i+1) Body)
          | vsubs i (TyAbs(Bvar,Body)) = TyAbs(Bvar,vsubs (i+1) Body)
          | vsubs i t = t
        fun subs i ty =
          case peek(fmap,ty)
           of SOME residue => lift i 0 residue
            | NONE =>
              (case ty
                of TyApp(opr,ty) => TyApp(subs i opr, subs i ty)
                 | TyAll(Bvar,Body) => TyAll(Bvar,subs (i+1) Body)
                 | TyAbs(Bvar,Body) => TyAbs(Bvar,subs (i+1) Body)
                 | _ => ty)
    in
      (if b then vsubs else subs) 0
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
  | polymorphic (TyAll (_,Body))  = true (* alt: polymorphic Body *)
  | polymorphic (TyAbs (_,Body))  = true (* alt: polymorphic Body *)
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


(* ---------------------------------------------------------------------*)
(* Beta conversion section, including conversionals for depth search    *)
(* ---------------------------------------------------------------------*)

fun beta_conv_ty (TyApp(M as TyAbs _, N))
       = let val (btyv,body) = dest_abs_type M
         in raw_type_subst [btyv |-> N] body
         end
  | beta_conv_ty _ = raise ERR "beta_conv_ty" "not a type beta redex"

fun eta_conv_ty (ty as TyAbs (tyv, TyApp(M, TyBv 0)))
       = let val a = TyFv tyv
             val M' = fst (dest_app_type (beta_conv_ty (TyApp(ty, a))))
                      handle HOL_ERR _ => raise ERR "eta_conv_ty" "not a type eta redex"
         in if mem a (type_vars M') then raise ERR "eta_conv_ty" "not a type eta redex"
            else M'
         end
  | eta_conv_ty _ = raise ERR "eta_conv_ty" "not a type eta redex"

exception UNCHANGEDTY;

fun qconv_ty c ty = c ty handle UNCHANGEDTY => ty

(* ---------------------------------------------------------------------*)
(* rand_conv_ty conv ``:t2 t1`` applies conv to t2                      *)
(* ---------------------------------------------------------------------*)

fun rand_conv_ty conv (TyApp(Rator,Rand)) = let
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
  TyApp(Rator, Newrand)
end
  | rand_conv_ty _ _ = raise ERR "rand_conv_ty" "not a type app"

(* ---------------------------------------------------------------------*)
(* rator_conv_ty conv ``:t2 t1`` applies conv to t1                     *)
(* ---------------------------------------------------------------------*)

fun rator_conv_ty conv (TyApp(Rator,Rand)) = let
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
  TyApp(Newrator, Rand)
end
  | rator_conv_ty _ _ = raise ERR "rator_conv_ty" "not a type app"

(* ---------------------------------------------------------------------*)
(* app_conv_ty conv ``:t2 t1`` applies conv to t1 and to t2             *)
(* ---------------------------------------------------------------------*)

fun app_conv_ty conv (TyApp(Rator, Rand)) = let in
  let
    val Rator' = conv Rator
  in
    TyApp(Rator', conv Rand) handle UNCHANGEDTY => TyApp(Rator', Rand)
  end handle UNCHANGEDTY => TyApp(Rator, conv Rand)
  end
  | app_conv_ty _ _ = raise ERR "app_conv_ty" "Not a type app"

(* ----------------------------------------------------------------------
    abs_conv_ty conv ``: \'a. t['a]`` applies conv to t['a]
   ---------------------------------------------------------------------- *)

fun abs_conv_ty conv (TyAbs(Bvar,Body)) = let
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
  TyAbs(Bvar, Newbody)
end
  | abs_conv_ty _ _ = raise ERR "abs_conv_ty" "not a type abstraction"

(* ----------------------------------------------------------------------
    univ_conv_ty conv ``: !'a. t['a]`` applies conv to t['a]
   ---------------------------------------------------------------------- *)

fun univ_conv_ty conv (TyAll(Bvar,Body)) = let
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
  TyAll(Bvar, Newbody)
end
  | univ_conv_ty _ _ = raise ERR "univ_conv_ty" "not a universal type"

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
   in if aconv_ty ty ty1 then raise ERR "changed_conv_ty" "Input type unchanged"
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

val deep_eta_conv_ty = qconv_ty (top_depth_conv_ty eta_conv_ty)

val deep_beta_eta_conv_ty = qconv_ty (top_depth_conv_ty (beta_conv_ty orelse_ty eta_conv_ty))

fun strip_app_beta_eta_type ty = strip_app_type (deep_beta_eta_conv_ty ty)

(*  head_beta1_ty reduces the head beta redex; fails if one does not exist. *)
fun head_beta1_ty ty = (rator_conv_ty head_beta1_ty orelse_ty beta_conv_ty) ty

(*  head_beta_ty repeatedly reduces any head beta redexes; never fails *)
(*  result has at its top level its actual shape *)
val head_beta_ty = qconv_ty (repeat_ty head_beta1_ty)


fun abconv_ty t1 t2 = aconv_ty (deep_beta_conv_ty t1) (deep_beta_conv_ty t2)

fun subtype t1 t2 = asubtype (deep_beta_conv_ty t1) (deep_beta_conv_ty t2)


(*---------------------------------------------------------------------------
       Higher order matching (from jrh via Michael Norrish - June 2001)
       Adapted to HOL-Omega types by PVH - July 18, 2008
 ---------------------------------------------------------------------------*)

local
  fun MERR s = raise ERR "raw_match_type error" s
  exception NOT_FOUND
  val eq_ty = abconv_ty (* beta-reduction NOT ASSUMMED before entering these functions *)
  fun find_residue red [] = raise NOT_FOUND
    | find_residue red ({redex,residue}::rest) = if red = redex then residue
                                                    else find_residue red rest
  fun find_residue_ty red [] = raise NOT_FOUND
    | find_residue_ty red ({redex,residue}::rest) = if eq_ty red redex then residue
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
    if eq_ty residue z then l
    else raise ERR "safe_insert_tya" "match"
  end handle NOT_FOUND => n::l
(*
  fun safe_insert_tya (n as {redex,residue}) l = let
    val residue' = deep_beta_eta_conv_ty residue
    val n' = redex |-> residue'
  in let
    val z = find_residue_ty redex l
  in
    if eq_ty residue' z then l
    else raise ERR "safe_insert_tya" "match"
  end handle NOT_FOUND => n'::l
  end
*)
  val mk_dummy_ty = let
    val name = dest_vartype(gen_tyvar())
  in fn (kd,rk) => with_flag (varcomplain,false) mk_vartype_opr(name, kd, rk)
  end
  fun rator_type ty = fst (dest_app_type ty)


  fun type_pmatch lconsts env pat ob sofar
      = type_pmatch_1 lconsts env (head_beta_ty pat) (head_beta_ty ob) sofar

  and type_pmatch_1 lconsts env (TyBv i) (TyBv j) sofar
      = if i=j then sofar
        else MERR "bound type variable mismatch"
    | type_pmatch_1 lconsts env (TyBv _) _ sofar
      = MERR "bound type variable mismatch"
    | type_pmatch_1 lconsts env _ (TyBv _) sofar
      = MERR "bound type variable mismatch"
    | type_pmatch_1 lconsts env vty cty (sofar as (insts,homs)) =
    if is_vartype vty then let
        val cty' = find_residue_ty vty env
      in
        if eq_ty cty' cty then sofar else MERR "type variable mismatch"
      end handle NOT_FOUND =>
                 if HOLset.member(lconsts, vty) then
                   if cty = vty then sofar
                   else MERR "can't instantiate local constant type"
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
            val vkd = kd_of vty (map (kind_of o #redex  ) env)
            val vrk = rk_of vty (map (rank_of o #redex  ) env)
            val ckd = kd_of cty (map (kind_of o #residue) env)
            val crk = rk_of cty (map (rank_of o #residue) env)
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


fun get_rank_kind_insts avoids (env:(hol_type,hol_type)subst) L (rk,(kdS,Id)) =
 itlist (fn {redex,residue} => fn (rk,Theta) =>
          (raw_match_rank (rk_of redex   (map (rank_of o #redex  ) env))
                          (rk_of residue (map (rank_of o #residue) env)) rk,
           raw_match_kind (kd_of redex   (map (kind_of o #redex  ) env))
                          (kd_of residue (map (kind_of o #residue) env)) Theta))
       L (rk,(kdS,union avoids Id))

fun separate_insts_ty lift rk kdavoids kdS env
         (insts :{redex : hol_type, residue : hol_type} list) = let
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
  val (rkin,kdins) = get_rank_kind_insts kdavoids env realinsts (rk,kdS)
in
  (betacounts,
   mapfilter (fn {redex = x, residue = t} => let
                   val x' = let val (xs,xkd,xrk) = dest_vartype_opr x
                            in with_flag (varcomplain,false)
                              mk_vartype_opr(xs, kind_subst (#1 kdins) xkd, xrk + rkin)
                            end
                 in
                   if t = x' then raise ERR "separate_insts_ty" ""
                             else {redex = if lift then x' else x, residue = t}
             end) realinsts,
   kdins,
   rkin)
end


fun kdenv_in_dom x (env, idlist) = mem x idlist orelse in_dom x env
fun kdenv_find_residue x (env, idlist) = if mem x idlist then x
                                         else find_residue x env
fun kdenv_safe_insert (t as {redex,residue}) (E as (env, idlist)) = let
  val existing = kdenv_find_residue redex E
in
  if existing = residue then E else raise ERR "kdenv_safe_insert" "Kind bindings clash"
end handle NOT_FOUND => if redex = residue then (env, redex::idlist)
                        else (t::env, idlist)


fun all_abconv [] [] = true
  | all_abconv [] _ = false
  | all_abconv _ [] = false
  | all_abconv (h1::t1) (h2::t2) = eq_ty h1 h2 andalso all_abconv t1 t2


fun type_homatch kdavoids lconsts rkin kdins (insts, homs) = let
  (* local constants of kinds and types never change *)
  val (var_homs,nvar_homs) = partition (fn (env,cty,vty) => is_vartype vty) homs
  fun args_are_fixed (env,cty,vty) = let
       val (vhop, vargs) = strip_app_type vty
       val afvs = type_varsl vargs
    in all (fn a => can (find_residue_ty a) env orelse can (find_residue_ty a) insts
                    orelse HOLset.member(lconsts, a)) afvs
    end
  val (real_homs,basic_homs) = partition args_are_fixed nvar_homs
  fun homatch rkin kdins (insts, homs) = 
  if homs = [] then insts
  else let
      val (env,cty,vty) = hd homs
    in
      if is_vartype vty then
        if eq_ty cty vty then homatch rkin kdins (insts, tl homs)
        else let
            val vkd = kind_of vty (* kd_of vty (map (kind_of o #redex  ) env) *)
            val vrk = rank_of vty (* rk_of vty (map (rank_of o #redex  ) env) *)
            val ckd = kd_of cty (map (kind_of o #residue) env)
            val crk = rk_of cty (map (rank_of o #residue) env)
            val newrkin  = raw_match_rank vrk crk rkin
            val newkdins = kdenv_safe_insert (vkd |-> ckd) kdins
            val newinsts = safe_insert_tya (vty |-> cty) insts (* (vty |-> cty)::insts *)
          in
            homatch newrkin newkdins (newinsts, tl homs)
          end
      else (* vty not a type var *) let
          val (vhop, vargs) = strip_app_type vty (* vhop should be a type variable *)
          val afvs = type_varsl vargs
          val inst_fn = inst_rank_kind rkin (fst kdins)
        in
          (let
             val tyins =
                 map (fn a =>
                         (inst_fn a |->
                                  (find_residue_ty a env
                                   handle _ =>
                                          find_residue_ty a insts
                                   handle _ =>
                                          if HOLset.member(lconsts, a)
                                          then a
                                          else raise ERR "type_homatch" "not bound"))) afvs
             val pats0 = map inst_fn vargs
             val pats = map (type_subst tyins) pats0
             val vhop' = inst_fn vhop
             val icty = list_mk_app_type(vhop', pats)
             val ni = let
               val (chop,cargs) = strip_app_type cty
             in
               if all_abconv cargs pats then
                 if eq_ty chop vhop then insts
                 else safe_insert_tya (vhop |-> chop) insts
               else let
                   val ginsts = map (fn p => (p |->
                                                (if is_vartype p then p
                                                 else gen_tyopvar(kd_of p (map (kind_of o #redex) env),
                                                                  rk_of p (map (rank_of o #redex) env)))))
                                    pats
                   val cty' = type_subst ginsts cty
                   val gvs = map #residue ginsts
                   val absty = list_mk_abs_type(gvs,cty')
                   val vinsts = safe_insert_tya (vhop |-> absty) insts
                   val icpair = (list_mk_app_type(vhop',gvs) |-> cty')
                 in
                   safe_insert_tya icpair vinsts
                   (* icpair::vinsts *)
                 end
             end
           in
             homatch rkin kdins (ni,tl homs)
           end) handle HOL_ERR _ => (let
                         val vhop' = inst_fn vhop
                         val chop = find_residue_ty vhop insts (* may raise NOT_FOUND *)
                         val _ = if eq_ty vhop' chop then raise NOT_FOUND else () (* avoid infinite recurse *)
                         val vhop_inst = [vhop' |-> chop]
                         val vty1 = deep_beta_conv_ty (type_subst vhop_inst (inst_fn vty))
                         val pinsts_homs' =
                             type_pmatch lconsts env vty1 cty (insts, tl homs)
                         val (rkin',kdins') =
                             get_rank_kind_insts kdavoids env
                                            (fst pinsts_homs')
                                            (0, ([], []))
                       in
                         homatch rkin' kdins' pinsts_homs'
                       end
                handle NOT_FOUND => let
                         val (lc,rc) = dest_app_type cty
                         val (lv,rv) = dest_app_type vty
                         val pinsts_homs' =
                             type_pmatch lconsts env rv rc
                                         (insts, (env,lc,lv)::(tl homs))
                         val (rkin',kdins') =
                             get_rank_kind_insts kdavoids env
                                            (fst pinsts_homs')
                                            (0, ([], []))
                       in
                         homatch rkin' kdins' pinsts_homs'
                       end)
        end
    end
in
  homatch rkin kdins (insts, var_homs @ real_homs @ basic_homs)
end

in

val type_pmatch = type_pmatch
val get_rank_kind_insts = get_rank_kind_insts
val type_homatch = type_homatch
val separate_insts_ty = separate_insts_ty

fun ho_match_type1 lift kdavoids lconsts vty cty insts_homs rk_kd_insts_ids = let
  val pinsts_homs = type_pmatch lconsts [] vty cty insts_homs
  val (rkin,kdins) = get_rank_kind_insts kdavoids [] (fst pinsts_homs) rk_kd_insts_ids
  val insts = type_homatch kdavoids lconsts rkin kdins pinsts_homs
in
  separate_insts_ty lift rkin kdavoids kdins [] insts
end

fun ho_match_type0 lift kdavoids lconsts vty cty = let
  val (bcs, tyins, kdins, rkin) = ho_match_type1 lift kdavoids lconsts vty cty ([], []) (0, ([], []))
in
  (tyins, fst kdins, rkin)
end handle e => raise (wrap_exn "HolKernel" "ho_match_type" e)

fun check_achieves_target (tyins, kdins, rkin) vty cty = 
(**)
  if abconv_ty (type_subst tyins (inst_rank_kind rkin kdins vty)) cty then ()
  else raise ERR "ho_match_type" "higher-order type matching failed to achieve target type"
(**)

fun ho_match_type kdavoids lconsts vty cty = let
  val vty' = deep_beta_conv_ty vty
  val cty' = deep_beta_conv_ty cty
  val (tyins, kdins, rkin) = ho_match_type0 true kdavoids lconsts vty' cty'
  val _ = check_achieves_target (tyins, kdins, rkin) vty' cty'
in (tyins, kdins, rkin)
end

end (* local *)

(* We redefine the main type matching functions here to use higher order matching. *)

fun prim_kind_match_type pat ob ((tyS,tyId), (kdS,kdId), rkS) =
    let val tyfixed = HOLset.addList(empty_tyset, tyId)
        val (_,tyS',(kdS',kdId'),rkS') = ho_match_type1 false kdId tyfixed pat ob (tyS,[]) (rkS,(kdS,kdId))
     in ((tyS',tyId), (kdS',kdId'), rkS')
    end;

fun raw_kind_match_type pat ob ((tyS,tyId), (kdS,kdId), rkS) =
    let val tyfixed = HOLset.addList(empty_tyset, tyId)
        val (_,tyS',(kdS',kdId'),rkS') = ho_match_type1 true kdId tyfixed pat ob (tyS,[]) (rkS,(kdS,kdId))
        val _ = check_achieves_target (tyS', kdS', rkS') pat ob
        val tyId' = Lib.subtract (Lib.union (type_vars pat) tyId) (map #redex tyS')
     in ((tyS',tyId'), (kdS',kdId'), rkS')
    end;

fun clean_subst ((tyS,_),(kdS,_),rkS) =
 let fun del A [] = A
       | del A ({redex,residue}::rst) =
         del (if abconv_ty residue redex then A else (redex |-> residue)::A) rst
 in (del [] tyS,kdS,rkS)
 end

fun kind_match_type pat ob =
      clean_subst (raw_kind_match_type pat ob (([],[]), ([],[]), 0))

fun raw_match_type pat ob (tyS,tyId) =
    let val ((tyS',tyId'),(kdS',kdId'),rkS') =
              raw_kind_match_type pat ob ((tyS,tyId),([],[]),0)
    in if null kdS' andalso null kdId' andalso rkS' = 0 then (tyS',tyId')
       else raise ERR "raw_match_type"
                  "kind and/or rank variable matches: use raw_kind_match_type instead"
    end;

fun match_type_restr fixed pat ob  = fst (raw_match_type pat ob ([],fixed))
fun match_type_in_context pat ob S = fst (raw_match_type pat ob (S,[]))

fun match_type pat ob = fst (raw_match_type pat ob ([],[]))


(*---------------------------------------------------------------------------
   Redefine the comparison relations and substitution functions
   to involve beta reduction for external use.
 ---------------------------------------------------------------------------*)

val raw_dom_rng = dom_rng
val dom_rng = fn ty => raw_dom_rng ty handle HOL_ERR _ => raw_dom_rng (deep_beta_conv_ty ty)

(*
val compare = fn (t1,t2) => compare(deep_beta_conv_ty t1, deep_beta_conv_ty t2)
val empty_tyset = HOLset.empty compare
fun type_eq t1 t2 = compare(t1,t2) = EQUAL;
*)

fun mapsub f = map (fn {redex,residue} => {redex=f redex, residue=residue})
val type_subst = fn s => type_subst (mapsub deep_beta_conv_ty s);

val raw_ty_sub = ty_sub
fun ty_sub theta ty = let val ty' = type_subst theta ty
                      in if type_eq ty ty' then SAME
                                           else DIFF ty'
                      end;


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

fun size acc tylist =
    case tylist of
      [] => acc
    | [] :: tys => size acc tys
    | (ty::tys1) :: tys2 => let
      in
        case ty of
          TyApp(opr, arg) => size acc ((opr :: arg :: tys1) :: tys2)
        | TyAll(_, body)  => size (1 + acc) ((body :: tys1) :: tys2)
        | TyAbs(_, body)  => size (1 + acc) ((body :: tys1) :: tys2)
        | _               => size (1 + acc) (tys1 :: tys2)
      end

fun type_size ty = size 0 [[ty]]

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
          ( add_string "("; pp Rand1;
            add_string " ->"; add_break(1,0);
            pp Rand2; add_string ")" )
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

fun sprint pp x = PP.pp_to_string 80 pp x

val type_to_string = sprint pp_raw_type;

(*
val _ = installPP Kind.pp_kind;
val _ = installPP pp_raw_type;
*)

end (* Type *)
