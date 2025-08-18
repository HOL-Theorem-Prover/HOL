(* ===================================================================== *)
(* FILE          : Term.sml                                              *)
(* DESCRIPTION   : ML-style typed lambda terms (no ML "let" though).     *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : August 26, 1991                                       *)
(* Modified      : September 22, 1997, Ken Larsen (functor removal)      *)
(* Rewritten     : 1999, Bruno Barras, to use explicit substitutions     *)
(* Modified      : July 2000, Konrad Slind, for Moscow ML 2.00           *)
(* ===================================================================== *)

structure Term :> Term =
struct

open Feedback Lib Subst KernelTypes

val kernelid = "stdknl"

type 'a set = 'a HOLset.set;
type ('a,'b) fmap = ('a,'b) HOLdict.dict;

val ERR = mk_HOL_ERR "Term";
val WARN = HOL_WARNING "Term";

val --> = Type.-->;
infixr 3 -->;

infix |-> ##;

(*---------------------------------------------------------------------------
               Create the signature for HOL terms
 ---------------------------------------------------------------------------*)


val termsig = KernelSig.new_table()
fun prim_delete_const kn = ignore (KernelSig.retire_name(termsig, kn))
fun prim_new_const (k as {Thy,Name}) ty = let
  val hty = if Type.polymorphic ty then POLY ty else GRND ty
  val id = KernelSig.insert(termsig, k, hty)
in
  Const(id, hty)
end
fun del_segment s = KernelSig.del_segment(termsig, s)

(*---------------------------------------------------------------------------*
 * Builtin constants. These are in every HOL signature, and it is            *
 * convenient to nail them down here.                                        *
 *---------------------------------------------------------------------------*)

local
  open KernelSig Type
  val eq_ty = POLY (alpha --> alpha --> bool)
  val hil_ty = POLY ((alpha --> bool) --> alpha)
  val imp_ty = GRND (bool --> bool --> bool)
in
  val eq_id = insert(termsig,{Name = "=", Thy = "min"}, eq_ty)
  val hil_id = insert(termsig,{Name = "@", Thy = "min"}, hil_ty)
  val imp_id = insert(termsig,{Name = "==>", Thy = "min"}, imp_ty)

  val eqc = Const (eq_id,eq_ty)
  val equality = eqc
  val hil = Const (hil_id,hil_ty)
  val imp = Const (imp_id,imp_ty)
end

(*---------------------------------------------------------------------------*
    Useful functions to hide explicit substitutions
    Important invariant: never delay subst on atoms, and compose Clos.
    Therefore, in Clos{Env,Body}, Body is either a Comb or an Abs.
    This invariant is enforced if we always use mk_clos instead of Clos.
 ---------------------------------------------------------------------------*)

fun mk_clos (s, Bv i) =
      (case (Subst.exp_rel(s,i))
        of (0, SOME t) => t
         | (k, SOME t) => mk_clos (Subst.shift(k,Subst.id), t)
         | (v, NONE)   => Bv v)
  | mk_clos (s, t as Fv _)     = t
  | mk_clos (s, t as Const _)  = t
  | mk_clos (s,Clos(Env,Body)) = Clos(Subst.comp mk_clos (s,Env), Body)
  | mk_clos (s,t)              = Clos(s, t)
;

(*---------------------------------------------------------------------------
    Propagate substitutions so that we are sure the head of the term is
    not a delayed substitution.
 ---------------------------------------------------------------------------*)

fun push_clos (Clos(E, Comb(f,x))) = Comb(mk_clos(E,f), mk_clos(E,x))
  | push_clos (Clos(E, Abs(v,M)))  = Abs(v, mk_clos (Subst.lift(1,E),M))
  | push_clos _ = raise ERR "push_clos" "not a subst"
;

(*---------------------------------------------------------------------------*
 * Computing the type of a term.                                             *
 *---------------------------------------------------------------------------*)

local fun lookup 0 (ty::_)  = ty
        | lookup n (_::rst) = lookup (n-1) rst
        | lookup _ []       = raise ERR "type_of" "lookup"
      fun ty_of (Fv(_,Ty)) _           = Ty
        | ty_of (Const(_,GRND Ty)) _   = Ty
        | ty_of (Const(_,POLY Ty)) _   = Ty
        | ty_of (Bv i) E               = lookup i E
        | ty_of (Comb(Rator, _)) E     = snd(Type.dom_rng(ty_of Rator E))
        | ty_of (t as Clos _) E        = ty_of (push_clos t) E
        | ty_of (Abs(Fv(_,Ty),Body)) E = Ty --> ty_of Body (Ty::E)
        | ty_of _ _ = raise ERR "type_of" "term construction"
in
fun type_of tm = ty_of tm []
end;


(*---------------------------------------------------------------------------
                Discriminators
 ---------------------------------------------------------------------------*)

fun is_bvar (Bv _)    = true | is_bvar _  = false;
fun is_var  (Fv _)    = true | is_var _   = false;
fun is_const(Const _) = true | is_const _ = false;
fun is_comb(Comb _) = true | is_comb(Clos(_,Comb _)) = true | is_comb _ = false
fun is_abs(Abs _) = true | is_abs(Clos(_,Abs _)) = true | is_abs _ = false;


(*---------------------------------------------------------------------------*
 * The type variables of a lambda term. Tail recursive (from Ken Larsen).    *
 *---------------------------------------------------------------------------*)

local fun tyV (Fv(_,Ty)) k         = k (Type.type_vars Ty)
        | tyV (Bv _) k             = k []
        | tyV (Const(_,GRND _)) k  = k []
        | tyV (Const(_,POLY Ty)) k = k (Type.type_vars Ty)
        | tyV (Comb(Rator,Rand)) k = tyV Rand (fn q1 =>
                                     tyV Rator(fn q2 => k (union q2 q1)))
        | tyV (Abs(Bvar,Body)) k   = tyV Body (fn q1 =>
                                     tyV Bvar (fn q2 => k (union q2 q1)))
        | tyV (t as Clos _) k      = tyV (push_clos t) k
in
fun type_vars_in_term tm = tyV tm Lib.I
end;

(*---------------------------------------------------------------------------*
 * The free variables of a lambda term. Tail recursive (from Ken Larsen).    *
 *---------------------------------------------------------------------------*)

local fun FV (v as Fv _) A k   = k (Lib.insert v A)
        | FV (Comb(f,x)) A k   = FV f A (fn q => FV x q k)
        | FV (Abs(_,Body)) A k = FV Body A k
        | FV (t as Clos _) A k = FV (push_clos t) A k
        | FV _ A k = k A
in
fun free_vars tm = FV tm [] Lib.I
end;

(*---------------------------------------------------------------------------*
 * The free variables of a lambda term, in textual order.                    *
 *---------------------------------------------------------------------------*)

fun free_vars_lr tm =
  let fun FV ((v as Fv _)::t) A   = FV t (Lib.insert v A)
        | FV (Bv _::t) A          = FV t A
        | FV (Const _::t) A       = FV t A
        | FV (Comb(M,N)::t) A     = FV (M::N::t) A
        | FV (Abs(_,M)::t) A      = FV (M::t) A
        | FV ((M as Clos _)::t) A = FV (push_clos M::t) A
        | FV [] A = rev A
  in
     FV [tm] []
  end;

(*---------------------------------------------------------------------------*
 * The set of all variables in a term, represented as a list.                *
 *---------------------------------------------------------------------------*)

local fun vars (v as Fv _) A        = Lib.insert v A
        | vars (Comb(Rator,Rand)) A = vars Rand (vars Rator A)
        | vars (Abs(Bvar,Body)) A   = vars Body (vars Bvar A)
        | vars (t as Clos _) A      = vars (push_clos t) A
        | vars _ A = A
in
fun all_vars tm = vars tm []
end;

fun free_varsl tm_list = itlist (union o free_vars) tm_list []
fun all_varsl tm_list  = itlist (union o all_vars) tm_list [];

(*---------------------------------------------------------------------------
     Support for efficient term variable sets and maps
 ---------------------------------------------------------------------------*)

fun fast_term_eq (t1:term) (t2:term) = Portable.pointer_eq (t1,t2)

fun var_compare (v1 as Fv(s1,ty1), v2 as Fv(s2,ty2)) =
    if fast_term_eq v1 v2 then
       EQUAL
    else
       (case String.compare (s1,s2)
         of EQUAL => Type.compare (ty1,ty2)
          | x => x)
  | var_compare _ = raise ERR "var_compare" "variables required";

val empty_varset = HOLset.empty var_compare
val empty_var_map = HOLdict.mkDict var_compare

fun var_map_of theta =
  let fun itFn {redex,residue} fmap =
        if not (is_var redex andalso type_of redex = type_of residue) then
           raise ERR "var_map_of" ""
        else
           HOLdict.insert(fmap,redex,residue)
  in
      rev_itlist itFn theta empty_var_map
  end


(* ----------------------------------------------------------------------
    A total ordering on terms that respects alpha equivalence.
    Fv < Bv < Const < Comb < Abs
   ---------------------------------------------------------------------- *)

fun compare (p as (t1,t2)) =
    if fast_term_eq t1 t2 then EQUAL else
    case p of
      (t1 as Clos _, t2)     => compare (push_clos t1, t2)
    | (t1, t2 as Clos _)     => compare (t1, push_clos t2)
    | (u as Fv _, v as Fv _) => var_compare (u,v)
    | (Fv _, _)              => LESS
    | (Bv _, Fv _)           => GREATER
    | (Bv i, Bv j)           => Int.compare (i,j)
    | (Bv _, _)              => LESS
    | (Const _, Fv _)        => GREATER
    | (Const _, Bv _)        => GREATER
    | (Const(c1,ty1),
       Const(c2,ty2))        => (case KernelSig.id_compare (c1, c2)
                                  of EQUAL => Type.compare (to_hol_type ty1,
                                                            to_hol_type ty2)
                                   | x => x)
    | (Const _, _)           => LESS
    | (Comb(M,N),Comb(P,Q))  => (case compare (M,P)
                                  of EQUAL => compare (N,Q)
                                   | x => x)
    | (Comb _, Abs _)        => LESS
    | (Comb _, _)            => GREATER
    | (Abs(Fv(_, ty1),M),
       Abs(Fv(_, ty2),N))    => (case Type.compare(ty1,ty2)
                                  of EQUAL => compare (M,N)
                                   | x => x)
    | (Abs _, _)             => GREATER;

fun term_eq t1 t2 = compare(t1,t2) = EQUAL

(*---------------------------------------------------------------------------
     Support for efficient general term sets and maps
 ---------------------------------------------------------------------------*)

val empty_tmset = HOLset.empty compare
val empty_term_map = HOLdict.mkDict compare

fun term_map_of theta =
  let fun itFn {redex,residue} (fmap,vardom) =
        if type_of redex <> type_of residue then
           raise ERR "term_map_of" "type mismatch in element of input"
        else
           (HOLdict.insert(fmap,redex,residue), is_var redex andalso vardom)
  in
     rev_itlist itFn theta (empty_term_map,true)
  end

(* ----------------------------------------------------------------------
    All "atoms" (variables (bound or free) and constants).

    Does not respect alpha-equivalence
   ---------------------------------------------------------------------- *)

fun all_atomsl tlist A =
    case tlist of
        [] => A
      | t::ts =>
        let
        in
          case t of
              Fv _ => all_atomsl ts (HOLset.add(A,t))
            | Const _ => all_atomsl ts (HOLset.add(A,t))
            | Comb(Rator,Rand) => all_atomsl (Rator::Rand::ts) A
            | Abs(v,body) => all_atomsl (body::ts) (HOLset.add(A,v))
            | Clos _ => all_atomsl (push_clos t::ts) A
            | Bv _ => all_atomsl ts A
        end

fun all_atoms t = all_atomsl [t] empty_tmset

(*---------------------------------------------------------------------------
        Free variables of a term. Tail recursive. Returns a set.
 ---------------------------------------------------------------------------*)

fun FVL [] A = A
  | FVL ((v as Fv _)::rst) A      = FVL rst (HOLset.add(A,v))
  | FVL (Comb(Rator,Rand)::rst) A = FVL (Rator::Rand::rst) A
  | FVL (Abs(_,Body)::rst) A      = FVL (Body::rst) A
  | FVL ((t as Clos _)::rst) A    = FVL (push_clos t::rst) A
  | FVL (_::rst) A                = FVL rst A


(* ----------------------------------------------------------------------
    free_in tm M : does tm occur free in M?
   ---------------------------------------------------------------------- *)

fun free_in tm =
   let fun f1 (Comb(Rator,Rand)) = (f2 Rator) orelse (f2 Rand)
         | f1 (Abs(_,Body)) = f2 Body
         | f1 (t as Clos _) = f2 (push_clos t)
         | f1 _ = false
       and f2 t = term_eq t tm orelse f1 t
   in f2
   end;

(*---------------------------------------------------------------------------
     The following are used in Thm to check side conditions (e.g.,
     does variable v occur free in the assumptions).
 ---------------------------------------------------------------------------*)

fun var_occurs M =
  let val v = (case M of Fv v => v | _ => raise ERR "" "")
      fun occ (Fv u)             = (v=u)
        | occ (Bv _)             = false
        | occ (Const _)          = false
        | occ (Comb(Rator,Rand)) = occ Rand orelse occ Rator
        | occ (Abs(_,Body))      = occ Body
        | occ (t as Clos _)      = occ (push_clos t)
   in occ end
   handle HOL_ERR _ => raise ERR "var_occurs" "not a variable";


(*---------------------------------------------------------------------------*
 * Making variables                                                          *
 *---------------------------------------------------------------------------*)

val mk_var = Fv

fun dest_var (Fv v) = v
  | dest_var _ = raise ERR "dest_var" "not a var"

fun inST s = not(null(KernelSig.listName termsig s))

(*---------------------------------------------------------------------------*
 *   "genvars" are a Lisp-style "gensym" for HOL variables.                  *
 *---------------------------------------------------------------------------*)

local val genvar_prefix = "%%genvar%%"
      fun num2name i = genvar_prefix^Int.toString i
      val num_stream = Portable.make_counter{init=0,inc=1}
in
fun genvar ty = Fv(num2name(num_stream()), ty)

fun genvars ty =
 let fun gen acc n = if n <= 0 then rev acc else gen (genvar ty::acc) (n-1)
 in gen []
 end

fun is_genvar (Fv(Name,_)) = String.isPrefix genvar_prefix Name
  | is_genvar _ = false;
end;


(*---------------------------------------------------------------------------*
 * Given a variable and a list of variables, if the variable does not exist  *
 * on the list, then return the variable. Otherwise, rename the variable and *
 * try again. Note well that the variant uses only the name of the variable  *
 * as a basis for testing equality. Experience has shown that basing the     *
 * comparison on both the name and the type of the variable resulted in      *
 * needlessly confusing formulas occasionally being displayed in interactive *
 * sessions.                                                                 *
 *---------------------------------------------------------------------------*)

fun gen_variant P caller =
  let fun var_name _ (Fv(Name,_)) = Name
        | var_name caller _ = raise ERR caller "not a variable"
      fun vary vlist (Fv(Name,Ty)) =
          let val L = map (var_name caller) vlist
              fun loop s =
                  if mem s L orelse P s then loop (s ^ "'")
                  else s
          in mk_var(loop Name, Ty)
          end
        | vary _ _ = raise ERR caller "2nd argument should be a variable"
  in vary
  end;

val variant      = gen_variant inST "variant"
val prim_variant = gen_variant (K false) "prim_variant";

fun numvariant avoids (Fv(Name,Ty)) =
    let
      fun var_name (Fv(Name,_)) = Name
        | var_name _ =
             raise ERR "numvariant" "Avoids list contains non-variable"
      val nms = map var_name avoids
      fun vary s = let val s' = Lexis.tmvar_vary s
                   in
                     if inST s' then vary s' else s'
                   end
    in
      Fv(Lexis.gen_variant vary nms Name, Ty)
    end
  | numvariant _ _ =
      raise ERR "numvariant" "2nd argument should be a variable"

fun mk_primed_var (Name,Ty) =
    gen_variant inST "mk_primed_var" [] (Fv(Name,Ty))

(*---------------------------------------------------------------------------*
 *             Making constants.                                             *
 *                                                                           *
 * We grab the constant scheme from the signature. If it is ground, then     *
 * we just return the scheme. Thus there will only be one copy of any        *
 * ground constant. If it is polymorphic, we match its type against the      *
 * given type. If the match is the identity substitution, we just return     *
 * the constant. If the match moves some variables, then we check that the   *
 * instance is ground (and then return GRND); otherwise the type is still    *
 * polymorphic.                                                              *
 *---------------------------------------------------------------------------*)

fun decls nm =
    let
      fun f ({Name,...}, info as (_, ty), A) =
          if nm = Name andalso Type.uptodate_type (to_hol_type ty) then
            Const info :: A
          else A
    in
      KernelSig.foldl f [] termsig
    end

fun prim_mk_const (knm as {Name,Thy}) =
 case KernelSig.peek(termsig, knm) of
     KernelSig.Success c => Const c
   | KernelSig.Failure (KernelSig.NoSuchThy _) =>
     raise ERR "prim_mk_const"
           ("Theory segment "^Lib.quote Thy^" not in ancestry")
   | _ =>
     raise ERR "prim_mk_const"
               (Lib.quote Name^" not found in theory "^Lib.quote Thy)

fun ground x = Lib.all (fn {redex,residue} => not(Type.polymorphic residue)) x;

fun create_const errstr (const as (_,GRND pat)) Ty =
      if Ty=pat then Const const
      else raise ERR "create_const" "not a type match"
  | create_const errstr (const as (r,POLY pat)) Ty =
     ((case Type.raw_match_type pat Ty ([],[])
        of ([],_) => Const const
         | (S,[]) => Const(r, if ground S then GRND Ty else POLY Ty)
         | (S, _) => Const(r,POLY Ty))
        handle HOL_ERR _ => raise ERR errstr
             (String.concat["Not a type instance: ", KernelSig.id_toString r]))


fun mk_thy_const {Thy,Name,Ty} = let
  val knm = {Thy=Thy,Name=Name}
  open KernelSig
in
  case peek(termsig, knm) of
      Failure(NoSuchThy _) => raise ERR "mk_thy_const" ("No such theory: " ^ Thy)
    | Success c => create_const "mk_thy_const" c Ty
    | _ => raise ERR "mk_thy_const" (KernelSig.name_toString knm^" not found")
end

fun first_decl fname Name =
  case KernelSig.listName termsig Name
   of [] => raise ERR fname (Name^" not found")
    | [(_, c)] => c
    | (_, c) :: _ =>
       (WARN fname (Lib.quote Name^": more than one possibility"); c)

fun mk_const(Name,Ty) = create_const "mk_const" (first_decl "mk_const" Name) Ty;

fun all_consts() =
    let
      fun buildAll (_, cinfo as (_,v), A) =
          if Type.uptodate_type (to_hol_type v) then Const cinfo :: A else A
    in
      KernelSig.foldl buildAll [] termsig
    end

fun thy_consts s =
    let
      fun buildthy ({Thy,...}, cinfo as (_, v), A) =
          if Thy = s andalso Type.uptodate_type (to_hol_type v) then
            Const cinfo :: A
          else A
    in
      KernelSig.foldl buildthy [] termsig
    end

fun same_const (Const(id1,_)) (Const(id2,_)) = id1 = id2
  | same_const _ _ = false

(*---------------------------------------------------------------------------*
 *        Making applications                                                *
 *---------------------------------------------------------------------------*)

local val INCOMPAT_TYPES  = Lib.C ERR "incompatible types"
      fun lmk_comb err =
        let fun loop (A,_) [] = A
              | loop (A,typ) (tm::rst) =
                 let val (ty1,ty2) = with_exn Type.dom_rng typ err
                 in if type_of tm = ty1
                    then loop(Comb(A,tm),ty2) rst
                    else raise err
                 end
        in fn (f,L) => loop(f, type_of f) L
        end
      val mk_comb0 = lmk_comb (INCOMPAT_TYPES "mk_comb")
in

fun mk_comb(r as (Abs(Fv(_,Ty),_), Rand)) =
      if type_of Rand = Ty then Comb r else raise INCOMPAT_TYPES "mk_comb"
  | mk_comb(r as (Clos(_,Abs(Fv(_,Ty),_)), Rand)) =
      if type_of Rand = Ty then Comb r else raise INCOMPAT_TYPES "mk_comb"
  | mk_comb(Rator,Rand) = mk_comb0 (Rator,[Rand])

val list_mk_comb = lmk_comb (INCOMPAT_TYPES "list_mk_comb")
end;

fun dest_comb (Comb r) = r
  | dest_comb (t as Clos _) = dest_comb (push_clos t)
  | dest_comb _ = raise ERR "dest_comb" "not a comb"

(*---------------------------------------------------------------------------*
 *                  Alpha conversion                                         *
 *---------------------------------------------------------------------------*)

fun rename_bvar s t =
    case t of
      Abs(Fv(_, Ty), Body) => Abs(Fv(s,Ty), Body)
    | Clos(_, Abs _) => rename_bvar s (push_clos t)
    | _ => raise ERR "rename_bvar" "not an abstraction";


local
  fun EQ(t1,t2) = fast_term_eq t1 t2
  fun subsEQ(s1,s2) = s1 = s2
in
fun aconv t1 t2 = EQ(t1,t2) orelse
 case(t1,t2)
  of (Comb(M,N),Comb(P,Q)) => aconv N Q andalso aconv M P
   | (Abs(Fv(_,ty1),M),
      Abs(Fv(_,ty2),N)) => ty1=ty2 andalso aconv M N
   | (Clos(e1,b1),
      Clos(e2,b2)) => (subsEQ(e1,e2) andalso EQ(b1,b2))
                       orelse aconv (push_clos t1) (push_clos t2)
   | (Clos _, _) => aconv (push_clos t1) t2
   | (_, Clos _) => aconv t1 (push_clos t2)
   | (M,N)       => (M=N)
end;

fun identical t1 t2 =
  t1 = t2 orelse
  case (t1,t2) of
      (Clos _, _) => identical (push_clos t1) t2
    | (_, Clos _) => identical t1 (push_clos t2)
    | (Const p1, Const p2) => p1 = p2
    | (Fv p1, Fv p2) => p1 = p2
    | (Bv i1, Bv i2) => i1 = i2
    | (Comb(t1,t2), Comb(ta,tb)) => identical t1 ta andalso identical t2 tb
    | (Abs(v1,t1), Abs (v2, t2)) => v1 = v2 andalso identical t1 t2
    | _ => false


(*---------------------------------------------------------------------------*
 *        Beta-reduction. Non-renaming.                                      *
 *---------------------------------------------------------------------------*)

fun beta_conv (Comb(Abs(_,Body), Bv 0)) = Body
  | beta_conv (Comb(Abs(_,Body), Rand)) =
     let fun subs((tm as Bv j),i)     = if i=j then Rand else tm
           | subs(Comb(Rator,Rand),i) = Comb(subs(Rator,i),subs(Rand,i))
           | subs(Abs(v,Body),i)      = Abs(v,subs(Body,i+1))
           | subs (tm as Clos _,i)    = subs(push_clos tm,i)
           | subs (tm,_) = tm
     in
       subs (Body,0)
     end
  | beta_conv (Comb(x as Clos _, Rand)) = beta_conv (Comb(push_clos x, Rand))
  | beta_conv (x as Clos _) = beta_conv (push_clos x)
  | beta_conv _ = raise ERR "beta_conv" "not a beta-redex";


(*---------------------------------------------------------------------------*
 *   Beta-reduction without propagation of the explicit substitution         *
 *   until the next abstraction.                                             *
 *---------------------------------------------------------------------------*)

fun lazy_beta_conv (Comb(Abs(_,Body),Rand)) =
      mk_clos(Subst.cons(Subst.id,Rand), Body)
  | lazy_beta_conv (Comb(Clos(Env, Abs(_,Body)),Rand)) =
      mk_clos(Subst.cons(Env,Rand), Body)
  | lazy_beta_conv (t as Clos _) = lazy_beta_conv (push_clos t)
  | lazy_beta_conv _ = raise ERR "lazy_beta_conv" "not a beta-redex";


(*---------------------------------------------------------------------------*
 *       Eta-conversion                                                      *
 *---------------------------------------------------------------------------*)

local fun pop (tm as Bv i, k) =
           if i=k then raise ERR "eta_conv" "not an eta-redex" else tm
        | pop (Comb(Rator,Rand),k) = Comb(pop(Rator,k), pop(Rand,k))
        | pop (Abs(v,Body), k)     = Abs(v,pop(Body, k+1))
        | pop (tm as Clos _, k)    = pop (push_clos tm, k)
        | pop (tm,k) = tm
      fun eta_body (Comb(Rator,Bv 0)) = pop (Rator,0)
        | eta_body (tm as Clos _)     = eta_body (push_clos tm)
        | eta_body _ = raise ERR "eta_conv" "not an eta-redex"
in
fun eta_conv (Abs(_,Body)) = eta_body Body
  | eta_conv (tm as Clos _)  = eta_conv (push_clos tm)
  | eta_conv _ = raise ERR "eta_conv" "not an eta-redex"
end;

(*---------------------------------------------------------------------------*)
(* Instantiate tyvars in a term, then instantiate term vars.                 *)
(*---------------------------------------------------------------------------*)

fun tag_type ty = if Type.polymorphic ty then POLY ty else GRND ty

val retag = delta_map tag_type

val delta_fv    = delta_binop Fv
val delta_const = delta_binop Const
val delta_comb  = delta_binop Comb
val delta_abs   = delta_binop Abs;

(*---------------------------------------------------------------------------*)
(* Rebuild term, except for re-use at type substitution                      *)
(*---------------------------------------------------------------------------*)

fun inst_ty_tm_0 theta tytheta =
  let val vmap = var_map_of theta
      fun fv_subst v = HOLdict.find(vmap,v) handle NotFound => v
      val tysubst = Type.type_subst tytheta
      fun fv_inst (Fv(s,ty)) = Fv(s,tysubst ty)
      val fvFn =
          if null tytheta then
             fv_subst
          else if null theta then
             fv_inst
          else
	     fv_subst o fv_inst
      fun isubst tm =
       case tm
        of Bv _ => tm
         | v as Fv _ => fvFn v
         | Const(_, GRND _) => tm
         | Const(r, POLY ty) => Const(r,tag_type(tysubst ty))
         | Comb(M,N) => Comb(isubst M,isubst N)
         | Abs(v,M) => Abs(fv_inst v, isubst M)
         | Clos _ => isubst(push_clos tm)
  in
    isubst
  end;

(*---------------------------------------------------------------------------*)
(* Rebuild term, except for re-use at atoms                                  *)
(*---------------------------------------------------------------------------*)

fun inst_ty_tm_1 theta tytheta =
  let val vmap = var_map_of theta
      fun fv_subst v = HOLdict.find(vmap,v) handle NotFound => v
      val tysubst = Type.ty_sub tytheta
      fun fv_inst (v as Fv(s,ty)) =
          (case tysubst ty
            of SAME => v
             | DIFF ty' => Fv(s,ty'))
      fun fv_inst_then_subst (v as Fv(s,ty)) =
          fv_subst (from_delta v (delta_fv (s,SAME) (ty, tysubst ty)))
      val fvFn =
          if null tytheta then
             fv_subst
          else if null theta then
             fv_inst
          else
	     fv_inst_then_subst
      fun isubst tm =
       case tm
        of Bv _ => tm
         | v as Fv _ => fvFn v
         | Const(_, GRND _) => tm
         | Const(r, tag as POLY ty) =>
            from_delta tm (delta_const (r,SAME) (tag,retag (tysubst ty)))
         | Comb(M,N) => Comb(isubst M,isubst N)
         | Abs(v,M) => Abs(fv_inst v, isubst M)
         | Clos _ => isubst(push_clos tm)
  in
    isubst
  end;

(*---------------------------------------------------------------------------*)
(* Space saving version via delta type                                       *)
(*---------------------------------------------------------------------------*)

fun inst_ty_tm_2 theta tytheta =
  let val vmap = var_map_of theta
      val tysubst = Type.ty_sub tytheta
      fun fv_subst v = (DIFF(HOLdict.find(vmap,v)) handle NotFound => SAME)
      fun fv_inst (Fv(s,ty)) = delta_map (curry Fv s) (tysubst ty)
      fun fv_inst_then_subst v =
          let val vdelta = fv_inst v
          in DIFF(HOLdict.find(vmap,from_delta v vdelta))
             handle NotFound => vdelta
           end
      val fvFn =
          if null tytheta then
             fv_subst
          else if null theta then
	     fv_inst
          else
             fv_inst_then_subst
     fun isubst tm =
       case tm
        of Bv _ => SAME
         | v as Fv _ => fvFn v
         | Const(_, GRND _) => SAME
         | Const(r, tag as POLY ty) =>
             delta_const (r,SAME) (tag, retag (tysubst ty))
         | Comb(M,N) => delta_comb (M,isubst M) (N,isubst N)
         | Abs(v,M)  => delta_abs (v,fv_inst v) (M,isubst M)
         | Clos _  => isubst(push_clos tm)
  in
    delta_apply isubst
  end;

(*---------------------------------------------------------------------------*)
(* Space saving via exceptions                                               *)
(*---------------------------------------------------------------------------*)

(*
fun grnd_tag_type (ty,grnd) = if grnd then GRND ty else POLY ty
val tysubst_grnd = Type.ty_sub_exn_grnd tytheta
*)

fun inst_ty_tm_3 theta tytheta =
  let val vmap = var_map_of theta
      fun fv_subst v = HOLdict.find(vmap,v) handle NotFound => nochange()
      fun fv_subst_total v = HOLdict.find(vmap,v) handle NotFound => v
      val tysubst = Type.ty_sub_exn tytheta
      fun fv_inst (Fv(s,ty)) = Fv(s,tysubst ty)
      fun fv_inst_then_subst v =
          (fv_subst_total (fv_inst v) handle Portable.NOCHANGE => fv_subst v)
      val fvFn =
          if null tytheta then
             fv_subst
          else if null theta then
             fv_inst
          else
             fv_inst_then_subst
      fun isubst tm =
       case tm
        of Bv _ => nochange()
         | v as Fv _ => fvFn v
         | Const(_, GRND _) => nochange()
         | Const(r, POLY ty) => Const(r, tag_type (tysubst ty))
         | Comb p => Comb(nochange_pair isubst isubst p)
         | Abs p  => Abs(nochange_pair fv_inst isubst p)
         | Clos _ => isubst(push_clos tm)
  in
    nochange_total isubst
  end

exception AGREE_ERR of
    (term,term) subst *
    (hol_type,hol_type) subst *
    term * term * term * term * term

fun inst_ty_tm_agree theta tytheta =
  let val fn0 = inst_ty_tm_0 theta tytheta
      val fn1 = inst_ty_tm_1 theta tytheta
      val fn2 = inst_ty_tm_2 theta tytheta
      val fn3 = inst_ty_tm_3 theta tytheta
  in
    fn tm =>
      let val tm0 = fn0 tm
          val tm1 = fn1 tm
          val tm2 = fn2 tm
	  val tm3 = fn3 tm
      in
         if identical tm0 tm1 andalso
            identical tm1 tm2 andalso
            identical tm2 tm3 then
            tm1
         else raise AGREE_ERR (theta,tytheta,tm,tm0,tm1,tm2,tm3)
       end
  end

(* Pick one of the above (for testing) *)

val iref = ref inst_ty_tm_agree;

(*
fun inst_ty_tm theta tytheta = !iref theta tytheta;
*)

val inst_ty_tm = inst_ty_tm_3;


(*---------------------------------------------------------------------------*)
(* inst and subst are instantiations of inst_ty_tm                           *)
(*---------------------------------------------------------------------------*)

fun inst tytheta = inst_ty_tm [] tytheta;

val var_pure = Lib.all (fn {redex,residue} => is_var redex)

(*---------------------------------------------------------------------------*)
(* subst further allows replacement of arbitrary terms                       *)
(*---------------------------------------------------------------------------*)

fun subst theta =
  if var_pure theta then
     inst_ty_tm theta []
  else
  let val (tmap,_) = term_map_of theta
      fun subs tm =
          HOLdict.find(tmap,tm)
          handle NotFound =>
            (case tm
              of Comb(M,N) => Comb(subs M, subs N)
               | Abs(v,M)  => Abs(v,subs M)
               | Clos _    => subs(push_clos tm)
               | otherwise => tm)
  in subs
  end


(*---------------------------------------------------------------------------
       Making abstractions. list_mk_binder is a relatively
       efficient version for making terms with many consecutive
       abstractions. Works by replacing all free vars to be bound by
       raw Bvs, then adding the binding prefix without going back into
       the body.
  ---------------------------------------------------------------------------*)
local
  fun binder_check binder = (* expect type to be (ty1 -> ty2) -> ty3 *)
     let val (fnty,rty) = Type.dom_rng(type_of binder)
         val _ = Type.dom_rng fnty
         val fntyV = Type.type_vars fnty
         val rtyV = Type.type_vars rty
     in
       if Lib.all (C mem fntyV) rtyV then (fnty,rty) else raise ERR "" ""
     end
     handle _ => raise ERR "list_mk_binder"
       "expected binder to have type ((ty1 -> ty2) -> ty3) where\
       \ tyvars of ty3 are all in (ty1->ty2)"
  fun binderFn NONE = (fn v => fn (M,_) => (Abs(v,M),Type.ind))
    | binderFn (SOME binder) =
       let val (dty,rty) = binder_check binder
       in fn v => fn (M,Mty) =>
             let val theta = Type.match_type dty (type_of v --> Mty)
             in (Comb (inst theta binder, Abs(v,M)),
                 Type.type_subst theta rty)
             end
       end
  open Redblackmap
  fun enum [] _ A = A
    | enum (h::t) i (vmap,rvs) = enum t (i-1) (insert (vmap,h,i),h::rvs)
  fun lookup v vmap = case peek (vmap,v) of NONE => v | SOME i => Bv i
  fun increment vmap = transform (fn x => x+1) vmap
  fun bind (v as Fv _) vmap k = k (lookup v vmap)
    | bind (Comb(M,N)) vmap k = bind M vmap (fn m =>
                                bind N vmap (fn n => k (Comb(m,n))))
    | bind (Abs(v,M)) vmap k  = bind M (increment vmap)
                                       (fn q => k (Abs(v,q)))
    | bind (t as Clos _) vmap k = bind (push_clos t) vmap k
    | bind tm vmap k = k tm
in
fun list_mk_binder opt =
 let val mk_binder = binderFn opt
 in fn (vlist,tm) =>
    if null vlist then
       tm
    else
    if not (List.all is_var vlist) then
       raise ERR "list_mk_binder" "expected list of variables"
    else
     (let val (vMap, rvlist) = enum vlist (length vlist-1) (mkDict compare, [])
          val raw_tm = bind tm vMap I
          val (final,_) = rev_itlist mk_binder rvlist (raw_tm,type_of tm)
      in
         final
      end
      handle e => raise wrap_exn "Term" "list_mk_binder" e)
 end
end;

val list_mk_abs = list_mk_binder NONE;

fun mk_abs(Bvar as Fv _, Body) =
    let fun bind (v as Fv _) i        = if v=Bvar then Bv i else v
          | bind (Comb(Rator,Rand)) i = Comb(bind Rator i, bind Rand i)
          | bind (Abs(Bvar,Body)) i   = Abs(Bvar, bind Body (i+1))
          | bind (t as Clos _) i      = bind (push_clos t) i
          | bind tm _ = tm (* constant *)
    in
      Abs(Bvar, bind Body 0)
    end
  | mk_abs _ = raise ERR "mk_abs" "Bvar not a variable"


(*---------------------------------------------------------------------------
            Taking terms apart

    These operations are all easy, except for taking apart multiple
    abstractions. It can happen, via beta-conversion or substitution,
    or instantiation, that a free variable is bound by the scope. One
    of the tasks of strip_abs is to sort the resulting mess out.
    strip_abs works by first classifying all the free variables in the
    body as being captured by the prefix bindings or not. Each capturing
    prefix binder is then renamed until it doesn't capture. Then we go
    through the body and replace the dB indices of the prefix with the
    corresponding free variables. These may in fact fall under another
    binder; the renaming of that will, if necessary, get done if that
    binder is taken apart (by a subsequent dest/strip_binder).
 ---------------------------------------------------------------------------*)

local fun peel f (t as Clos _) A = peel f (push_clos t) A
        | peel f tm A =
            case f tm of
              SOME(Abs(v,M)) => peel f M (v::A)
            | otherwise => (A,tm)
      datatype occtype = PREFIX of int | BODY
      fun array_to_revlist A =
        let val top = Array.length A - 1
            fun For i B = if i>top then B else For (i+1) (Array.sub(A,i)::B)
        in For 0 []
        end
      val vi_empty = HOLset.empty (fn ((v1,i1),(v2,i2)) => var_compare(v1,v2))
      fun add_vi viset vi =
         if HOLset.member(viset,vi) then viset else HOLset.add(viset,vi)
      fun trypush_clos (x as Clos _) = push_clos x
        | trypush_clos t = t
in
fun strip_binder opt =
 let val f =
         case opt of
           NONE => (fn (t as Abs _) => SOME t
                     | (t as Clos(_, Abs _)) => SOME (push_clos t)
                     | other => NONE)
               | SOME c => (fn t => let val (rator,rand) = dest_comb t
                                    in if same_const rator c
                                       then SOME (trypush_clos rand)
                                       else NONE
                                    end handle HOL_ERR _ => NONE)
 in fn tm =>
   let
     open Uref
     val (prefixl,body) = peel f tm []
     val AV = Uref.new (Redblackmap.mkDict String.compare) : ((string,occtype)Redblackmap.dict) Uref.t
     fun peekInsert (key,data) =
        let open Redblackmap
        in case peek (!AV,key)
            of SOME data' => SOME data'
             | NONE       => (AV := insert(!AV,key,data); NONE)
        end
     val prefix = Array.fromList prefixl
     val vmap = curry Array.sub prefix
     val (insertAVbody,insertAVprefix,lookAV,dupls) =
        let open Redblackmap  (* AV is red-black map  of (var,occtype) elems *)
            fun insertl [] _ dupls = dupls
              | insertl (x::rst) i dupls =
                  let val n = fst(dest_var x)
                  in case peekInsert (n,PREFIX i)
                      of NONE => insertl rst (i+1) (dupls)
                       | SOME _ => insertl rst (i+1) ((x,i)::dupls)
                  end
            val dupls = insertl prefixl 0 []
        in ((fn s => (AV := insert (!AV,s,BODY))),         (* insertAVbody *)
            (fn (s,i) => (AV := insert (!AV,s,PREFIX i))), (* insertAVprefix *)
            (fn s => peek (!AV,s)),                        (* lookAV *)
            dupls)
        end
     fun variantAV n =
         gen_variant (fn s => isSome (lookAV s)) "strip_binder" [] n
     fun CVs (v as Fv(n,_)) capt k =
          (case lookAV n
            of SOME (PREFIX i) => k (add_vi capt (vmap i,i))
             | SOME BODY => k capt
             | NONE => (insertAVbody n; k capt))
       | CVs(Comb(M,N)) capt k = CVs N capt (fn c => CVs M c k)
       | CVs(Abs(_,M)) capt k  = CVs M capt k
       | CVs(t as Clos _) capt k = CVs (push_clos t) capt k
       | CVs tm capt k = k capt
     fun unclash insert [] = ()
       | unclash insert ((v,i)::rst) =
           let val v' = variantAV v
               val n' = #1 (dest_var v')
           in Array.update(prefix,i,v')
            ; insert (n',i)
            ; unclash insert rst
           end
     fun unbind (v as Bv i) j k = k (vmap(i-j) handle Subscript => v)
       | unbind (Comb(M,N)) j k = unbind M j (fn m =>
                                  unbind N j (fn n => k(Comb(m,n))))
       | unbind (Abs(v,M)) j k  = unbind M (j+1) (fn q => k(Abs(v,q)))
       | unbind (t as Clos _) j k = unbind (push_clos t) j k
       | unbind tm j k = k tm
 in
     unclash insertAVprefix (List.rev dupls)
   ; unclash (insertAVbody o fst) (HOLset.listItems(CVs body vi_empty I))
   ; (array_to_revlist prefix, unbind body 0 I)
 end
 end
end;

val strip_abs = strip_binder NONE;

local exception CLASH
in
fun dest_abs(Abs(Bvar as Fv(Name,Ty), Body)) =
    let fun dest (v as (Bv j), i)     = if i=j then Bvar else v
          | dest (v as Fv(s,_), _)    = if Name=s then raise CLASH else v
          | dest (Comb(Rator,Rand),i) = Comb(dest(Rator,i),dest(Rand,i))
          | dest (Abs(Bvar,Body),i)   = Abs(Bvar, dest(Body,i+1))
          | dest (t as Clos _, i)     = dest (push_clos t, i)
          | dest (tm,_) = tm
    in (Bvar, dest(Body,0))
       handle CLASH =>
              dest_abs(Abs(variant (free_vars Body) Bvar, Body))
    end
  | dest_abs (t as Clos _) = dest_abs (push_clos t)
  | dest_abs _ = raise ERR "dest_abs" "not a lambda abstraction"
end;

local
open KernelSig
in
fun break_abs(Abs(_,Body)) = Body
  | break_abs(t as Clos _) = break_abs (push_clos t)
  | break_abs _ = raise ERR "break_abs" "not an abstraction";

fun dest_thy_const (Const(id,ty)) =
      let val {Name,Thy} = name_of_id id
      in {Thy=Thy, Name=Name, Ty=to_hol_type ty}
      end
  | dest_thy_const _ = raise ERR"dest_thy_const" "not a const"

fun break_const (Const p) = (I##to_hol_type) p
  | break_const _ = raise ERR "break_const" "not a const"

fun dest_const (Const(id,ty)) = (name_of id, to_hol_type ty)
  | dest_const _ = raise ERR "dest_const" "not a const"
end

(*---------------------------------------------------------------------------
               Derived destructors
 ---------------------------------------------------------------------------*)

fun rator (Comb(Rator,_)) = Rator
  | rator (Clos(Env, Comb(Rator,_))) = mk_clos(Env,Rator)
  | rator _ = raise ERR "rator" "not a comb"

fun rand (Comb(_,Rand)) = Rand
  | rand (Clos(Env, Comb(_,Rand))) = mk_clos(Env,Rand)
  | rand _ = raise ERR "rand" "not a comb"

val bvar = fst o dest_abs;
val body = snd o dest_abs;


(*---------------------------------------------------------------------------
    Matching (first order, modulo alpha conversion) of terms, including
    sets of variables and type variables to avoid binding.
 ---------------------------------------------------------------------------*)

local
  fun MERR s = raise ERR "raw_match_term" s
  fun free (Bv i) n             = i<n
    | free (Comb(Rator,Rand)) n = free Rand n andalso free Rator n
    | free (Abs(_,Body)) n      = free Body (n+1)
    | free (t as Clos _) n      = free (push_clos t) n
    | free _ _ = true
  fun lookup x ids =
   let fun look [] = if HOLset.member(ids,x) then SOME x else NONE
         | look ({redex,residue}::t) = if x=redex then SOME residue else look t
   in look end
  fun bound_by_scope scoped M = if scoped then not (free M 0) else false
  val tymatch = Type.raw_match_type
  open KernelSig
in
fun RM [] theta = theta
  | RM (((v as Fv(n,Ty)),tm,scoped)::rst) ((S1 as (tmS,Id)),tyS)
     = if bound_by_scope scoped tm
       then MERR "Attempt to capture bound variable"
       else RM rst
            ((case lookup v Id tmS
               of NONE => if v=tm then (tmS,HOLset.add(Id,v))
                                  else ((v |-> tm)::tmS,Id)
                | SOME tm' => if aconv tm' tm then S1
                              else MERR ("double bind on variable "^
                                         Lib.quote n)),
             tymatch Ty (type_of tm) tyS)
  | RM ((Const(c1,ty1),Const(c2,ty2),_)::rst) (tmS,tyS)
      = RM rst
        (if c1 <> c2 then
          let val n1 = id_toString c1
              val n2 = id_toString c2
          in
           MERR ("Different constants: "^n1^" and "^n2)
          end
         else
         case (ty1,ty2)
          of (GRND _, POLY _) => MERR"ground const vs. polymorphic const"
           | (GRND pat,GRND obj) => if pat=obj then (tmS,tyS)
                       else MERR"const-const with different (ground) types"
           | (POLY pat,GRND obj) => (tmS, tymatch pat obj tyS)
           | (POLY pat,POLY obj) => (tmS, tymatch pat obj tyS))
  | RM ((Abs(Fv(_,ty1),M),Abs(Fv(_,ty2),N),_)::rst) (tmS,tyS)
      = RM ((M,N,true)::rst) (tmS, tymatch ty1 ty2 tyS)
  | RM ((Comb(M,N),Comb(P,Q),s)::rst) S = RM ((M,P,s)::(N,Q,s)::rst) S
  | RM ((Bv i,Bv j,_)::rst) S  = if i=j then RM rst S
                                 else MERR "Bound var doesn't match"
  | RM (((pat as Clos _),ob,s)::t) S = RM ((push_clos pat,ob,s)::t) S
  | RM ((pat,(ob as Clos _),s)::t) S = RM ((pat,push_clos ob,s)::t) S
  | RM all others                    = MERR "different constructors"
end

fun raw_match tyfixed tmfixed pat ob (tmS,tyS)
   = RM [(pat,ob,false)] ((tmS,tmfixed), (tyS,tyfixed));

fun norm_subst ((tmS,_),(tyS,_)) =
 let val Theta = inst tyS
     fun del A [] = A
       | del A ({redex,residue}::rst) =
         del (let val redex' = Theta(redex)
              in if residue=redex' then A else (redex' |-> residue)::A
              end) rst
 in (del [] tmS,tyS)
 end

fun match_terml tyfixed tmfixed pat ob =
 norm_subst (raw_match tyfixed tmfixed pat ob ([],[]))

val match_term = match_terml [] empty_varset;

(*---------------------------------------------------------------------------
       Must know that ty is the type of tm1 and tm2.
 ---------------------------------------------------------------------------*)

fun prim_mk_eq ty tm1 tm2 = Comb(Comb(inst [Type.alpha |-> ty] eqc, tm1), tm2)

(*---------------------------------------------------------------------------
      Must know that tm1 and tm2 both have type "bool"
 ---------------------------------------------------------------------------*)

fun prim_mk_imp tm1 tm2  = Comb(Comb(imp, tm1),tm2);

(*---------------------------------------------------------------------------
      Take an equality apart, and return the type of the operands
 ---------------------------------------------------------------------------*)

local val err = ERR "dest_eq_ty" ""
in
fun dest_eq_ty t =
 let val ((c,M),N) = with_exn ((dest_comb##I) o dest_comb) t err
 in if same_const c eqc
       then (M,N,fst(Type.dom_rng (type_of c)))
       else raise err
 end
end;

(*---------------------------------------------------------------------------
   Full propagation of substitutions.
 ---------------------------------------------------------------------------*)

local val subs_comp = Subst.comp mk_clos
  fun vars_sigma_norm (s,t) =
    case t of
      Comb(Rator,Rand) => Comb(vars_sigma_norm(s, Rator),
                               vars_sigma_norm(s, Rand))
    | Bv i =>
        (case Subst.exp_rel(s,i) of
           (0, SOME v)   => vars_sigma_norm (Subst.id, v)
         | (lams,SOME v) => vars_sigma_norm (Subst.shift(lams,Subst.id),v)
         | (lams,NONE)   => Bv lams)
    | Abs(Bvar,Body) => Abs(Bvar, vars_sigma_norm  (Subst.lift(1,s), Body))
    | Fv _ => t
    | Clos(Env,Body) => vars_sigma_norm (subs_comp(s,Env), Body)
    | _ => t  (* i.e., a const *)
in
fun norm_clos tm = vars_sigma_norm(Subst.id,tm)
end

fun size acc tlist =
    case tlist of
      [] => acc
    | t :: ts => let
      in
        case t of
          Comb(t1,t2) => size (1 + acc) (t1 :: t2 :: ts)
        | Abs(_, b) => size (1 + acc) (b :: ts)
        | Clos _ => size acc (push_clos t :: ts)
        | _ => size (1 + acc) ts
      end
fun term_size t = size 0 [t]

(*---------------------------------------------------------------------------*
 * Traverse a term, performing a given (side-effecting) operation at the     *
 * leaves. For our purposes, bound variables can be ignored.                 *
 *---------------------------------------------------------------------------*)

fun trav f =
  let fun trv (a as Fv _) = f a
        | trv (a as Const _) = f a
        | trv (Comb(Rator,Rand)) = (trv Rator; trv Rand)
        | trv (Abs(Bvar,Body))   = (trv Bvar; trv Body)
        | trv _ = ()
  in
    trv o norm_clos
  end;

(*---------------------------------------------------------------------------*
 *  Raw syntax prettyprinter for terms.                                      *
 *---------------------------------------------------------------------------*)

val app     = "@"
val lam     = "|"
val dollar  = "$"
val percent = "%"

fun strip_comb t =
    let fun recurse t A =
            case t of
                Comb(f,x) => recurse f (x::A)
              | _ => (t, A)
    in
      recurse t []
    end

datatype pptask = ppTM of term | ppLAM | ppAPP of int | ppS of string
fun pp_raw_term index tm = let
  fun mkAPP [] = [ppAPP 1]
    | mkAPP (ppAPP n :: rest) = ppAPP (n + 1) :: rest
    | mkAPP rest = ppAPP 1 :: rest
  fun pp acc tasklist =
      case tasklist of
          [] => String.concat (List.rev acc)
        | ppTM (Abs(Bvar, Body)) :: rest =>
            pp acc (ppTM Bvar :: ppTM Body :: ppLAM :: rest)
        | ppTM (t as Comb(Rator, Rand)) :: rest =>
          let
            val (f, args) = strip_comb t
          in
            if is_abs f then
              pp acc (ppTM Rator :: ppTM Rand :: mkAPP rest)
            else
              let
                val (letter1,letter2,i) = case f of Bv i => ("u", "b", i)
                                                  | _ => ("U", "B", index f)
              in
                case args of
                    [x] => pp acc (ppTM x :: ppS (letter1 ^ Int.toString i) ::
                                   rest)
                  | [x,y] =>
                    pp acc (ppTM x::ppTM y::
                            ppS (letter2 ^ Int.toString i)::rest)
                  | _ => pp acc (ppTM Rator :: ppTM Rand :: mkAPP rest)
              end
          end
        | ppTM (Bv i) :: rest =>
            pp (dollar ^ Int.toString i :: acc) rest
        | ppTM a :: rest =>
            pp (percent ^ Int.toString (index a) :: acc) rest
        | ppLAM :: rest => pp (lam :: acc) rest
        | ppAPP n :: rest =>
            pp (app ^ (if n = 1 then "" else Int.toString n) :: acc) rest
        | ppS s :: rest =>  pp (s :: acc) rest
in
  pp [] [ppTM tm]
end

fun write_raw index tm = pp_raw_term index (norm_clos tm)

(*---------------------------------------------------------------------------*
 * Fetching theorems from disk. The following parses the "raw" term          *
 * representation found in exported theory files.                            *
 *---------------------------------------------------------------------------*)

local
datatype lexeme
   = app of int
   | lamb
   | ident of int
   | bvar  of int
   | BV1 of int
   | BV2 of int
   | I1 of int
   | I2 of int

local val numeric = Char.contains "0123456789"
in
fun take_numb ss0 =
  let val (ns, ss1) = Substring.splitl numeric ss0
  in case Int.fromString (Substring.string ns)
      of SOME i => (i,ss1)
       | NONE   => raise ERR "take_numb" ""
  end
end;

(* don't allow numbers to be split across fragments *)

fun lexer ss1 =
  case Substring.getc ss1 of
    NONE => NONE
  | SOME (c,ss2) =>
    case c of
        #"|" => SOME(lamb,  ss2)
      | #"%"  => let val (n,ss3) = take_numb ss2 in SOME(ident n, ss3) end
      | #"$"  => let val (n,ss3) = take_numb ss2 in SOME(bvar n,  ss3) end
      | #"U"  => let val (n,ss3) = take_numb ss2 in SOME(I1 n,  ss3) end
      | #"u"  => let val (n,ss3) = take_numb ss2 in SOME(BV1 n,  ss3) end
      | #"B"  => let val (n,ss3) = take_numb ss2 in SOME(I2 n,  ss3) end
      | #"b"  => let val (n,ss3) = take_numb ss2 in SOME(BV2 n,  ss3) end
      | #"@" =>
        (let val (n,ss3) = take_numb ss2 in SOME(app n, ss3) end
         handle HOL_ERR _ => SOME (app 1, ss2))
      |   _   => raise ERR "raw lexer" "bad character";

in
fun read_raw tmv = let
  fun index i = Vector.sub(tmv, i)
  fun parse (stk,ss) =
      case (stk, lexer ss) of
        (_, SOME (bvar n,  rst)) => parse (Bv n::stk,rst)
      | (_, SOME (ident n, rst)) => parse (index n::stk,rst)
      | (stk, SOME (app n, rst)) => doapps n stk rst
      | (t::stk, SOME (I1 n, rst)) => parse (Comb(index n, t) :: stk, rst)
      | (t::stk, SOME (BV1 n, rst)) => parse (Comb(Bv n, t) :: stk, rst)
      | (t2::t1::stk, SOME (I2 n, rst)) =>
          parse (Comb(Comb(index n, t1), t2) :: stk, rst)
      | (t2::t1::stk, SOME (BV2 n, rst)) =>
          parse (Comb(Comb(Bv n, t1), t2) :: stk, rst)
      | (bd::bv::stk, SOME(lam,rst)) => parse (Abs(bv,bd)::stk, rst)
      | (_, SOME(lam, _)) => raise ERR "read_raw" "lam: small stack"
      | ([tm], NONE) => tm
      | ([], NONE) => raise ERR "read_raw" "eof: empty stack"
      | (_, NONE) => raise ERR "read_raw" "eof: large stack"
  and doapps n stk rst =
      if n = 0 then parse (stk,rst)
      else
        case stk of
            x::f::stk => doapps (n - 1) (Comb(f,x)::stk) rst
          | _ =>  raise ERR "read_raw" "app: small stack"

in
fn s => parse ([], Substring.full s)
end
end (* local *)

(* ----------------------------------------------------------------------
    Is a term up-to-date wrt the theory?
   ---------------------------------------------------------------------- *)

fun uptodate_term t = let
  open Type
  fun recurse tmlist =
      case tmlist of
        [] => true
      | t::rest => let
        in
          case t of
            Fv(_, ty) => Type.uptodate_type ty andalso recurse rest
          | Const(info, ty) => KernelSig.uptodate_id info andalso
                               uptodate_type (to_hol_type ty) andalso
                               recurse rest
          | Comb(f,x) => recurse (f::x::rest)
          | Abs(v,bod) => recurse (v::bod::rest)
          | Bv _ => recurse rest
          | Clos _ => recurse (push_clos t :: rest)
        end
in
  recurse [t]
end

datatype lambda =
     VAR of string * hol_type
   | CONST of {Name: string, Thy: string, Ty: hol_type}
   | COMB of term * term
   | LAMB of term * term

fun dest_term M =
  case M of
      Const _ => CONST (dest_thy_const M)
    | Fv p => VAR p
    | Comb p => COMB p
    | Abs _ => LAMB (dest_abs M)
    | Clos _ => dest_term (push_clos M)
    | Bv _ => raise Fail "dest_term applied to bound variable"

end (* Term *)
