(* ===================================================================== *)
(* FILE          : term.sml                                              *)
(* DESCRIPTION   : Simply typed lambda terms.                            *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : August 26, 1991                                       *)
(* UPDATE        : October 94. Term signature implementation moved from  *)
(*                 symtab.sml, which is now gone.                        *)
(* Modified      : September 22, 1997, Ken Larsen                        *)
(* ===================================================================== *)

structure Term :> Term =
struct

open Exception Lib;

val --> = Type.-->; infixr 3 -->; infix |->;

fun TERM_ERR function message =
 Exception.HOL_ERR{origin_structure = "Term",
                   origin_function = function,
                   message = message};


(*---------------------------------------------------------------------------*
 * HOL terms are represented internally using deBruijn indices. Externally,  *
 * they appear to be in name-carrying syntax.                                *
 *---------------------------------------------------------------------------*)

datatype term = Fv of {Name:string, Ty:Type.hol_type}
              | Bv of int
              | Const of string ref * Type.hol_type
              | Comb of {Rator:term, Rand:term}
              | Abs of {Bvar:term, Body:term}
              | Clos of {Env:term Subst.subs, Body:term};


(*---------------------------------------------------------------------------*
 * Useful functions to hide substitutions                                    *
 *---------------------------------------------------------------------------*)
fun is_clos (Clos _) = true | is_clos _ = false;

(* Important invariant: never delay subst on atoms, and compose Clos.
 * Therefore, in Clos{Env,Body}, Body is either a Comb or an Abs.
 * This invariant is enforced if we always use mk_clos instead of Clos.
 *)
fun mk_clos (s, Bv i) =
        (case (Subst.exp_rel(s,i)) of
          (0, SOME t) => t
        | (k, SOME t) => mk_clos (Subst.shift(k,Subst.id), t)
        | (v, NONE)   => Bv v)
  | mk_clos (s, t as Fv _)      = t
  | mk_clos (s, t as Const _)   = t
  | mk_clos (s, Clos{Env,Body}) =
      Clos{Env=Subst.comp mk_clos (s,Env), Body=Body}
  | mk_clos (s, t)              = Clos{Env=s, Body=t}
;

val subs_comp = Subst.comp mk_clos;

(* Propagate substitutions so that we are sure the head of the term is
 * not a delayed substitution.
 *)
fun push_clos (Clos{Env, Body=Comb{Rator,Rand}}) =
        Comb{Rator = mk_clos(Env,Rator), Rand = mk_clos(Env,Rand)}
  | push_clos (Clos{Env, Body=Abs{Bvar,Body}}) =
        Abs{Bvar = Bvar, Body = mk_clos (Subst.lift(1,Env), Body)}
  | push_clos _ = raise TERM_ERR "push_clos" "not a subst"
;


(*---------------------------------------------------------------------------*
 * Computing the type of a term.                                             *
 *---------------------------------------------------------------------------*)
local fun range ty = case (Type.dest_type ty)
                      of {Tyop="fun", Args=[_,rty]} => rty
                       | _ => raise TERM_ERR "type_of%range" ""
      fun lookup 0 (ty::_)  = ty
        | lookup n (_::rst) = lookup (n-1) rst
        | lookup _ []       = raise TERM_ERR "type_of" "lookup"
      fun ty_of (Fv{Ty, ...}) _      = Ty
        | ty_of (Const(_,Ty)) _      = Ty
        | ty_of (Bv i)        E      = lookup i E
        | ty_of (Comb{Rator, ...}) E = range (ty_of Rator E)
        | ty_of (Abs{Bvar = Fv{Ty,...},Body}) E = Ty --> ty_of Body (Ty::E)
	| ty_of (t as Clos _) E = ty_of (push_clos t) E
        | ty_of _ _ = raise TERM_ERR "type_of" "term construction"
in
  fun type_of tm = ty_of tm []
end;


(*---------------------------------------------------------------------------*
 * The type variables of a lambda term.                                      *
 *---------------------------------------------------------------------------*)
fun type_vars_in_term (Fv{Ty, ...}) = Type.type_vars Ty
  | type_vars_in_term (Const(_,Ty)) = Type.type_vars Ty
  | type_vars_in_term (Comb{Rator,Rand}) = union (type_vars_in_term Rator)
                                                 (type_vars_in_term Rand)
  | type_vars_in_term (Abs{Bvar,Body}) = union (type_vars_in_term Bvar)
                                               (type_vars_in_term Body)
  | type_vars_in_term (t as Clos _) = type_vars_in_term (push_clos t)
  | type_vars_in_term (Bv _) = [];


(*---------------------------------------------------------------------------*
 * The free variables of a lambda term. This could be implemented more       *
 * efficiently, say by an ordered list.                                      *
 *---------------------------------------------------------------------------*)
local
fun frees(v as Fv _) free_list =
      if (mem v free_list) then free_list else v::free_list
  | frees(Comb{Rator, Rand}) free_list = frees Rand (frees Rator free_list)
  | frees(Abs{Body,...}) free_list = frees Body free_list
  | frees(t as Clos _) free_list = frees (push_clos t) free_list
  | frees _ free_list = free_list
in
  fun free_vars tm = frees tm []
end;


(*---------------------------------------------------------------------------*
 * The free variables of a lambda term, in textual order.                    *
 *---------------------------------------------------------------------------*)
fun free_vars_lr tm =
  let fun frees(v as Fv _) A = insert v A
        | frees(Comb{Rator, Rand}) A = frees Rator (frees Rand A)
        | frees(Abs{Body,...}) A = frees Body A
	| frees(t as Clos _) A = frees (push_clos t) A
        | frees _ A = A
  in frees tm []
end;


(*---------------------------------------------------------------------------*
 * The *set* of all variables in a term.                                     *
 *---------------------------------------------------------------------------*)
local fun vars (v as Fv _) vlist        = insert v vlist
        | vars(Comb{Rator, Rand}) vlist = vars Rand (vars Rator vlist)
        | vars(Abs{Bvar, Body}) vlist   = vars Body (vars Bvar vlist)
	| vars(t as Clos _) vlist       = vars (push_clos t) vlist
        | vars _ vlist = vlist
in
  fun all_vars tm = vars tm []
end;

fun free_varsl tm_list = itlist (union o free_vars) tm_list []
fun all_varsl tm_list  = itlist (union o all_vars) tm_list [];

(*---------------------------------------------------------------------------*
 * Does tm occur free in M. This is not defined modulo aconv. Maybe it       *
 * should be?                                                                *
 *---------------------------------------------------------------------------*)
fun free_in tm M =
   let fun f1 (Comb{Rator,Rand}) = (f2 Rator) orelse (f2 Rand)
         | f1 (Abs{Body,...}) = f2 Body
	 | f1 (t as Clos _) = f2 (push_clos t)
         | f1 _ = false
       and f2 t = (t=tm) orelse (f1 t)
   in f2 M
   end;


(*---------------------------------------------------------------------------*
 * A total ordering on terms.  Fv < Bv < Const < Comb < Abs                  *
 *---------------------------------------------------------------------------*)

local fun atom_lt {Name=(s1:string),Ty=ty1}  {Name=s2,Ty=ty2}
           = case String.compare (s1,s2)
              of LESS => true
               | EQUAL => Type.type_lt ty1 ty2
               | GREATER => false
in
fun term_lt (t1 as Clos _) t2 = term_lt (push_clos t1) t2
  | term_lt t1 (t2 as Clos _) = term_lt t1 (push_clos t2)

  | term_lt (Fv v1) (Fv v2) = atom_lt v1 v2
  | term_lt (Fv _) _ = true

  | term_lt (Bv _)  (Fv _)  = false
  | term_lt (Bv i1) (Bv i2) = i1<i2
  | term_lt (Bv _)     _    = true

  | term_lt (Const _) (Fv _) = false
  | term_lt (Const _) (Bv _) = false
  | term_lt (Const(ref n1,ty1))
            (Const(ref n2,ty2)) = atom_lt {Name=n1,Ty=ty1} {Name=n2,Ty=ty2}
  | term_lt (Const _) _ = true

  | term_lt (Comb{Rator=rator1,Rand=rand1})
            (Comb{Rator=rator2,Rand=rand2}) =
      term_lt rator1 rator2
      orelse (if (rator2=rator1) then term_lt rand1 rand2 else false)
  | term_lt (Comb _) (Abs _) = true
  | term_lt (Comb _) _ = false

  | term_lt (Abs{Bvar=bv1, Body=body1})
            (Abs{Bvar=bv2, Body=body2}) =
     term_lt bv1 bv2 orelse (if (bv2=bv1) then term_lt body1 body2 else false)
  | term_lt (Abs _) _ = false
end;


(*---------------------------------------------------------------------------*
 * It makes sense to declare the term construction primitive in the place    *
 * where the term signature is declared and manipulated. It makes sense to   *
 * declare and manipulate the logic signature in the structure Theory.       *
 * However, Theory is defined after theorems have been defined. It is also   *
 * necessary to have some knowledge of the term signature be a part of Term. *
 * Hence, I need a "backward" reference from Theory to Term.                 *
 *---------------------------------------------------------------------------*)
local val inST_ref  = ref (fn _:string => false)
      val mk_const_ref  = ref (fn _:{Name:string,Ty:Type.hol_type}
                                => Fv{Name="",Ty=Type.mk_vartype"'a"})
      val const_decl_ref  = ref (fn _:string =>
          {const = Fv{Name="",Ty=Type.mk_vartype"'a"},theory=""})
      val started = ref false
in
  fun init f g h = if !started then ()
                   else (inST_ref := f; mk_const_ref := g;
                         const_decl_ref := h; started := true);

  fun inST s = (!inST_ref) s;
  fun mk_const r = (!mk_const_ref) r;
  fun const_decl s = (!const_decl_ref) s;
end;

(*---------------------------------------------------------------------------*
 * Renaming support.                                                         *
 *---------------------------------------------------------------------------*)
local fun num2name s i = s^Lib.int_to_string i
in
fun subscripts x s =
   let val project = num2name (s^x)
       val cnt = ref 0
       fun incr() = (cnt := !cnt + 1; project (!cnt))
   in
     incr
   end
end;

fun primes s =
   let val current = ref s
       fun next () = (current := Lib.prime (!current); !current)
   in
     next
   end;

fun nameStrm s =
 (case !Globals.priming
   of NONE => primes
    | SOME x => subscripts x) s;


(*---------------------------------------------------------------------------*
 * Making variables                                                          *
 *---------------------------------------------------------------------------*)

val mk_var = Fv

fun mk_primed_var {Name,Ty} =
   let val next = nameStrm Name
       fun spin s = if (inST s) then spin (next()) else s
   in
     mk_var{Name=spin Name, Ty=Ty}
   end;


local fun num2name i = "%%genvar%%"^Lib.int_to_string i
      val nameStrm = Lib.mk_istream (fn x => x+1) 0 num2name
in
fun genvar ty = Fv{Name = state(next nameStrm), Ty = ty}
end;

fun genvars _ 0 = []
  | genvars ty n = genvar ty::genvars ty (n-1);

(*---------------------------------------------------------------------------*
 * Given a variable and a list of variables, if the variable does not exist  *
 * on the list, then return the variable. Otherwise, rename the variable and *
 * try again.                                                                *
 *---------------------------------------------------------------------------*)

local fun away L incr =
       let fun vary A [] s = s
             | vary A (h::t) s =
                case String.compare(h,s)
                 of LESS => vary A t s
                  | EQUAL => vary [] (A@t) (incr())
                  | GREATER => vary (h::A) t s
       in
          vary [] L
       end
      fun var_name(Fv{Name,...}) = Name
        | var_name _ = raise TERM_ERR "variant.var_name" "not a variable"
in
fun variant vlist (Fv{Name,Ty}) =
    let val next = nameStrm Name
        val awayf = away (map var_name vlist) next
        fun loop name =
           let val s = awayf name
           in if inST s then loop (next()) else s
           end
    in mk_var{Name=loop Name, Ty=Ty}
    end
  | variant _ _ = raise TERM_ERR "variant" "2nd arg. should be a variable"



(*---------------------------------------------------------------------------
     Returned value may have same name as a constant in the signature.
 ---------------------------------------------------------------------------*)

fun prim_variant [] v = v
  | prim_variant vlist (Fv{Name,Ty}) =
       mk_var{Name=away (map var_name vlist) (nameStrm Name) Name, Ty=Ty}
  | prim_variant _ _ = raise TERM_ERR "prim_variant"
                                      "2nd arg. should be a variable"
end;


(* Normalizing names (before pretty-printing with pp_raw, or trav) and full
 * propagation of substitutions, so that no 
 *)
fun vars_sigma_norm (s,t) =
  case t of
    Comb{Rator,Rand} =>
      let val (a,fva) = vars_sigma_norm (s,Rator)
	  val (b,fvb) = vars_sigma_norm (s,Rand)
      in (Comb{Rator = a, Rand = b}, union fva fvb)
      end
  | Bv i =>
      (case Subst.exp_rel(s,i) of
	(0, SOME v)    => vars_sigma_norm (Subst.id, v)
      |	(lams, SOME v) => vars_sigma_norm (Subst.shift(lams,Subst.id), v)
      |	(lams, NONE)   => (Bv lams, []))
  | Abs{Bvar,Body} =>
      let val (bd,fv) = vars_sigma_norm (Subst.lift(1,s), Body)
      in (Abs{Bvar = variant fv Bvar, Body = bd}, fv)
      end
  | Fv _ => (t,[t])
  | Clos{Env,Body} => vars_sigma_norm (subs_comp(s,Env), Body)
  | _ => (t, [])
;

fun norm_clos tm = fst (vars_sigma_norm(Subst.id,tm));



(*---------------------------------------------------------------------------
 * Making applications
 *---------------------------------------------------------------------------*)

local fun ERR s = TERM_ERR s "incompatible types"
      val INCOMPAT_TYPES  = ERR "list_mk_comb"
      val INCOMPAT_TYPES1 = ERR "mk_comb"
in
fun list_mk_comb (f,L) =
 let fun loop (A,_) [] = A
       | loop (A,typ) (tm::rst2) =
           let val (ty1,ty2) = Type.dom_rng typ
           in if (type_of tm = ty1)
              then loop(Comb{Rator=A,Rand=tm},ty2) rst2
              else raise INCOMPAT_TYPES
           end handle HOL_ERR _ => raise INCOMPAT_TYPES
 in
   loop(f,type_of f) L
 end

(*---------------------------------------------------------------------------
 * Special case when Rator is an abstraction - examine the type of
 * the bound variable.
 *---------------------------------------------------------------------------*)
fun mk_comb(r as {Rator = Abs{Bvar = Fv{Ty,...},...}, Rand}) =
      if (type_of Rand = Ty) then Comb r else raise INCOMPAT_TYPES1
  | mk_comb(r as {Rator = Clos{Body=Abs{Bvar=Fv{Ty,...},...},...}, Rand}) =
      if (type_of Rand = Ty) then Comb r else raise INCOMPAT_TYPES1
  | mk_comb{Rator,Rand} = list_mk_comb (Rator,[Rand])
                          handle HOL_ERR _ => raise INCOMPAT_TYPES1
end;


(*---------------------------------------------------------------------------*
 * Making abstractions.                                                      *
 *---------------------------------------------------------------------------*)
(*
local
val bv0  = Bv 0  val bv1  = Bv 1  val bv2=Bv 2 val bv3 = Bv 3 val bv4 = Bv 4
val bv5  = Bv 5  val bv6  = Bv 6  val bv7=Bv 7 val bv8=Bv 8 val bv9 = Bv 9
val bv10 = Bv 10 val bv11 = Bv 11 val bv12=Bv 12 val bv13=Bv 13 val bv14=Bv 14
val bv15 = Bv 15 val bv16 = Bv 16 val bv17 = Bv 17 val bv18 = Bv 18
val bv19 = Bv 19 val bv20 = Bv 20 val bv21 = Bv 21 val bv22 = Bv 22
val bv23 = Bv 23 val bv24 = Bv 24 val bv25 = Bv 25 val bv26 = Bv 26
val bv27 = Bv 27 val bv28 = Bv 28 val bv29 = Bv 29 val bv30 = Bv 30
val bv31 = Bv 31 val bv32 = Bv 32 val bv33 = Bv 33 val bv34 = Bv 34
in
fun mk_bv(1) = bv1 | mk_bv(2) = bv2 | mk_bv(3) = bv3 | mk_bv(4) = bv4
  | mk_bv(5) = bv5 | mk_bv(6) = bv6 | mk_bv(7) = bv7 | mk_bv(8) = bv8
  | mk_bv(9) = bv9 | mk_bv(10) = bv10 | mk_bv(11) = bv11 | mk_bv(12) = bv12
  | mk_bv(13) = bv13 | mk_bv(14) = bv14 | mk_bv(15) = bv15 | mk_bv(16) = bv16
  | mk_bv(17) = bv17 | mk_bv(18) = bv18 | mk_bv(19) = bv19 | mk_bv(20) = bv20
  | mk_bv(21) = bv21 | mk_bv(22) = bv22 | mk_bv(23) = bv23 | mk_bv(24) = bv24
  | mk_bv(25) = bv25 | mk_bv(26) = bv26 | mk_bv(27) = bv27 | mk_bv(28) = bv28
  | mk_bv(29) = bv29 | mk_bv(30) = bv30 | mk_bv(31) = bv31 | mk_bv(32) = bv32
  | mk_bv(33) = bv33 | mk_bv(34) = bv34 | mk_bv(n) = Bv(n)
end
*)

(* Does the above make any difference? *)
val mk_bv = Bv;

(*---------------------------------------------------------------------------
 * Make a lambda abstraction. Try for some sharing.
 *---------------------------------------------------------------------------*)
fun mk_abs{Bvar as Fv _, Body} =
 let fun bind (v as Fv _) i = if (v=Bvar) then mk_bv(i) else v
       | bind (Comb{Rator,Rand}) i = Comb{Rator=bind Rator i,Rand=bind Rand i}
       | bind (Abs{Bvar, Body=tm}) i = Abs{Bvar=Bvar, Body=bind tm (i+1)}
       | bind tm _ = tm
 in
   Abs{Bvar=Bvar, Body=bind Body 0}
 end
 | mk_abs _ = raise TERM_ERR "mk_abs" "Bvar not a variable";


fun dest_var (Fv v) = v
  | dest_var _ = raise TERM_ERR "dest_var" "not a var"
fun dest_const (Const (ref name,ty)) = {Name=name,Ty=ty}
  | dest_const _ = raise TERM_ERR"dest_const" "not a const"
fun dest_comb (Comb cmb) = cmb
  | dest_comb (t as Clos _) = dest_comb (push_clos t)
  | dest_comb _ = raise TERM_ERR "dest_comb" "not a comb"

local exception CLASH
in
fun dest_abs(Abs{Bvar as Fv{Name,Ty},Body}) =
   let fun dest (v as (Bv j), i) = if (i=j) then Bvar else v
         | dest (v as Fv{Name = s,...}, _) = 
               if (Name = s) then raise CLASH else v
         | dest (Comb{Rator,Rand},i) =
             Comb{Rator = dest(Rator,i), Rand = dest(Rand,i)}
         | dest (Abs{Bvar,Body},i) =
	     Abs{Bvar=Bvar,Body = dest(Body,i+1)}
	 | dest (t as Clos _, i) = dest (push_clos t, i)
         | dest (tm,_) = tm
   in {Bvar = Bvar, Body = dest(Body,0)}
      handle CLASH => 
      dest_abs(Abs{Bvar = variant (free_vars Body) Bvar,
		   Body = Body})
   end
  | dest_abs (t as Clos _) = dest_abs (push_clos t)
  | dest_abs _ = raise TERM_ERR "dest_abs" "not a lambda abstraction"
end;


(*---------------------------------------------------------------------------
      Type antiquotations (only required in term parser).
 ---------------------------------------------------------------------------*)
fun ty_antiq ty = Fv{Name="ty_antiq",Ty=ty}

fun dest_ty_antiq (Fv{Name="ty_antiq",Ty}) = Ty
  | dest_ty_antiq _ = raise TERM_ERR "dest_ty_antiq" "not a type antiquotation"

val is_ty_antiq = can dest_ty_antiq

(*---------------------------------------------------------------------------
 * Discriminators.
 *---------------------------------------------------------------------------*)
fun is_bvar (Bv _)    = true  | is_bvar _  = false;
fun is_var  (Fv _)    = true  | is_var _   = false;
fun is_const(Const _) = true  | is_const _ = false;
fun is_comb (Comb _)  = true 
  | is_comb (Clos{Body=Comb _,...}) = true
  | is_comb _  = false;
fun is_abs  (Abs _)   = true 
  | is_abs  (Clos{Body=Abs _,...}) = true
  | is_abs _   = false;

(*---------------------------------------------------------------------------
 * Derived operations
 *---------------------------------------------------------------------------*)
fun rator (Comb{Rator, ...}) = Rator
  | rator (Clos{Env, Body=Comb{Rator,...}}) = mk_clos(Env,Rator)
  | rator _ = raise TERM_ERR "rator" "not a comb"

fun rand (Comb{Rand, ...}) = Rand
  | rand (Clos{Env, Body=Comb{Rand,...}}) = mk_clos(Env,Rand)
  | rand _ = raise TERM_ERR "rand" "not a comb"

val bvar = #Bvar o dest_abs;
val body = #Body o dest_abs;

datatype 'a lambda = VAR   of {Name  : string, Ty : Type.hol_type}
                   | CONST of {Name  : string, Ty : Type.hol_type}
                   | COMB  of {Rator : 'a, Rand : 'a}
                   | LAMB  of {Bvar  : term, Body : 'a};

fun dest_term (Fv a) = VAR a
  | dest_term (Const(ref name,ty)) = CONST{Name=name,Ty=ty}
  | dest_term (Comb r) = COMB r
  | dest_term (a as Abs _) = LAMB(dest_abs a)
  | dest_term (t as Clos _) = dest_term (push_clos t)
  | dest_term (Bv _) = raise TERM_ERR "dest_term" "mangled term"

(*---------------------------------------------------------------------------*
 * fun aconv (Comb{Rator = M1, Rand = M2}) (Comb{Rator=N1,Rand=N2}) =        *
 *          aconv M1 N1 andalso aconv M2 N2                                  *
 *  | aconv (Abs{Bvar=Fv{Ty=ty1,...}, Body = body1})                         *
 *          (Abs{Bvar=Fv{Ty=ty2,...}, Body = body2}) =                       *
 *                         (ty1=ty2) andalso (aconv body1 body2)             *
 *  | aconv tm1 tm2 = (tm1=tm2);                                             *
 *---------------------------------------------------------------------------*)

local fun EQ (M,N) = Portable.pointer_eq(M,N)
in
fun aconv t1 t2 = EQ(t1,t2) orelse
(case(t1,t2) of
   (Comb{Rator=M,Rand=N},Comb{Rator=P,Rand=Q}) => aconv N Q andalso aconv M P
 | (Abs{Bvar=Fv{Ty=ty1,...}, Body=M},
    Abs{Bvar=Fv{Ty=ty2,...}, Body=N}) => (ty1=ty2) andalso (aconv M N)
 | (Clos{Env=e1,Body=b1}, Clos{Env=e2,Body=b2}) =>
     (EQ(e1,e2) andalso EQ(b1,b2)) orelse aconv (push_clos t1) (push_clos t2)
 | (Clos _, _) => aconv (push_clos t1) t2
 | (_, Clos _) => aconv t1 (push_clos t2)
 | (M,N) => (M=N))
end;

(* Is there a faster version of this? *)
fun term_compare tm1 tm2 =
    if (aconv tm1 tm2) then EQUAL
    else if term_lt tm1 tm2 then LESS else GREATER;



(*---------------------------------------------------------------------------
 * General term substitution. It's only this complicated because we rename.
 * Why, if we have dB terms? Because we want to be able to re-parse
 * prettyprinted terms, i.e., parse o pp = I
 *
 * When we are trying to replace in term M using a substitution theta,
 * we
 * 1. Go through the substitution checking that the types of the redex and
 *    residue are the same. (This could be lazified, but isn't.)
 *
 * 2. Start with M; try to find a {redex,incoming} record in theta s.t. redex
 *    is aconv with M. Since we are using dB terms, this automatically checks
 *    if M is free (modulo alpha convertibility).
 *
 * 3a. Suppose this isn't possible; recurse into the structure of M
 *
 * 3b. Suppose this is possible. Now we have some work to do.
 *
 *     1. Check that the free_variables of the residue are not bound by the
 *        current scope. If the scope is empty, there is no need to compute
 *        FV(residue). Otherwise, we compute the names of all free variables
 *        in residue (if that hasn't been done already), and store them in
 *        the cell "fn_residue" of the binding. Now we call function "itr"
 *        which iterates back in the scope, checking for each element "s" of
 *        the scope, whether it is a name of a free variable in residue. If
 *        it is, we have found a clash. However, our heuristic is to go to
 *        the "most outlying clash" (this allows a subtle optimization), so we
 *        iterate through the entire scope, keeping track of the index of the
 *        last clash. If we come out of the scope and there were no clashes,
 *        then we do the replacement. Otherwise, there was a clash;
 *        compute all the free variable names that could come in from theta
 *        (if it hasn't already been done). Then raise the CLASH exception,
 *        with the index of the lambda to propagate to. (This index allows
 *        us to ignore problems having to do with propagating back to the
 *        most outlying clash when there are duplicated variables in the
 *        scope, e.g., \x x.M.)
 *
 * 3a1. Suppose we were at an "\v.M" and we recursed into M, adding the name
 *      of v to the scope. We have to handle the CLASH exception.
 *
 *      - If it is 0, then we are the most outlying clash. We rename the bound
 *        variable to be different than "anything in sight", i.e., the scope
 *        (of the Abs), all the names of variables (free or bound) in M, and
 *        the names of all free variables that could possibly come in from
 *        theta. Now recurse. If there is a CLASH arising from this recursive
 *        call, it cannot possibly be a result of the newly chosen name,
 *        so simply decrement the index and propagate the CLASH. (This is
 *        our subtle optimization, since otherwise, the CLASH could have
 *        been from our newly chosen name, and we would have to again search
 *        for a new variable name at this node.)
 *
 *      - if it is not 0, then decrement the index and propagate.
 *
 *---------------------------------------------------------------------------*)

local
 fun check [] = ()
   | check ({redex,residue}::rst) =
       if (type_of redex = type_of residue) then check rst
       else raise TERM_ERR "subst" "redex has different type than residue"
 fun assc ([],_) = NONE
        | assc ({redex,residue}::rst, tm) =
                  if (aconv tm redex) then SOME residue else assc (rst,tm)
in
fun subst [] tm = tm
  | subst theta tm =
    let val _ = check theta
        fun subs tm =
          case assc (theta,tm) of
            SOME residue => residue
	  | NONE =>
	    (case tm of
	      Comb{Rator,Rand} => Comb{Rator=subs Rator, Rand=subs Rand}
            | Abs{Bvar,Body} => Abs{Bvar=Bvar,Body=subs Body}
	    | Clos _ => subs(push_clos tm)
            | _ => tm)
    in
      subs tm
    end
end;

(*----------------------------------------------------------------------------
 * Tests
 * Example from LCF code:
 *
 *   theta = { x'/z; x/y }  (* i.e., the parallel replacement of z by x'
 *                                   and y by x *)
 *   tm = "\x'. ((f y z) (\x. g x' x y z))"
     Term.subst [Term`z:bool` |-> Term`x':bool`,
                 Term`y:bool` |-> Term`x:bool`]
      (Term`(\x'. f (y:bool) (z:bool) (\x:bool. g x' x y z:bool)):bool->bool`);
 *    = "\x''. ((f x x') (\x'''. g x'' x''' x x'))"
 *
 *
 *Another tricky one:
 *   theta = { x'/y; x/z }
 *   tm = "\x. (f y z)"
     Term.subst [Term`y:bool` |-> Term`x':bool`,
                 Term`z:bool` |-> Term`x:bool`]
           (Term`\x:bool. f (y:bool) (z:bool) : bool`);
 *   = (--`\x''. f x' x`--) : term
 *
 *
    Term.subst [Term`y:bool` |-> Term`x:bool`]
               (Term`\x:bool.\x:bool.(y:bool)`);
 *  = (--`\x' x''. x`--) : Term.term
 *
 *
 *
    Term.subst [Term`x:bool` |-> Term`z':bool`,
                Term`y:bool` |-> Term`z:bool`]
               (Term`\z:bool. f (x:bool) (y:bool) (z:bool) : bool`);
 *  = (--`\z''. f z' z z''`--) : Term.term

 * This example shows that names alone are important, not types.

        subst [Term`x:bool` |-> Term`f (y:bool):bool`]
              (Term`\y :'a. (x:bool)`);
 * val it = (--`\y'. f y`--) : term

 * cut-down version of Klaus Schneider bug

      val tm = Term`\(p:'a) (q:'a). f (x:'a) (y:'a) : 'a`;
      val theta = [Term`x:'a` |-> Term`q:'a`,
                   Term`y:'a` |-> Term`p:'a`];
      subst theta tm;

 *   val it = (--`\p' q'. f q p`--) : term


 * And reverse, for thoroughness

     val tm = Term`\(p:'a) (q:'a). f (y:'a) (x:'a) : 'a`;
     val theta = [Term`x:'a` |-> Term`q:'a`,
                  Term`y:'a` |-> Term`p:'a`];
     subst theta tm;
 *   val it = (--`\p' q'. f p q`--) : term
 *
 * Now a recent one by Elsa Gunter:
 *
     load"pairTheory";
     val y  = Term`y:bool`;
     val y' = Term`y':bool`;
     val x  = Term`x:bool`;

     val tm = Term`\^y. (^x, \^y'.^y)`;
     subst [x |-> y] tm;
 *
 * `\y''. y,(\y'. y'')`
 *
 *
    beta_conv
        (Term`(\x y z. y x z z_1 z_2 y_1 y_2) (y z)`);
 *  val it = \y_3 z_3. y_3 (y z) z_3 z_1 z_2 y_1 y_2

 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 * Non-renaming betaconv.
 *---------------------------------------------------------------------------*)
fun beta_conv (Comb{Rator = Abs{Body,...}, Rand}) =
 let fun subs ((tm as Bv j),i) = if (i=j) then Rand else tm
       | subs (Comb{Rator,Rand},i) =
	   Comb{Rator=subs(Rator,i), Rand=subs(Rand,i)}
       | subs (Abs{Bvar as Fv{Name,Ty},Body},i) =
           Abs{Bvar=Bvar,Body=subs(Body,i+1)}
       | subs (tm as Clos _,i) = subs(push_clos tm,i)
       | subs (tm,_) = tm
 in
   subs (Body,0)
 end
| beta_conv _ = raise TERM_ERR "beta_conv" "not a beta-redex";


(* beta-reduction without propagation of the explicit substitution
 * until the next abstraction.
 *)
fun lazy_beta_conv (Comb{Rator=Abs{Body,...},Rand}) =
      mk_clos(Subst.cons(Subst.id,Rand), Body)
  | lazy_beta_conv (Comb{Rator=Clos{Env, Body=Abs{Body,...}},Rand}) =
      mk_clos(Subst.cons(Env,Rand), Body)
  | lazy_beta_conv (t as Clos _) = lazy_beta_conv (push_clos t)
  | lazy_beta_conv _ = raise TERM_ERR "lazy_beta_conv" "not a beta-redex";


(* eta-conversion: being in the kernel, it can be implemented without the
 * heavy dest_abs.
 *)
local
fun pop (t as Bv i, k) =
      if i=k then raise TERM_ERR "eta_conv" "not a eta-redex"
      else t
  | pop (Comb{Rator,Rand}, k) = Comb{Rator=pop(Rator,k), Rand=pop(Rand,k)}
  | pop (Abs{Bvar,Body}, k) = Abs{Bvar=Bvar,Body=pop(Body, k+1)}
  | pop (t as Clos _, k) = pop (push_clos t, k)
  | pop (t,k) = t
fun eta_body (Comb{Rator,Rand=Bv 0}) = pop (Rator,0)
  | eta_body (t as Clos _) = eta_body (push_clos t)
  | eta_body _ = raise TERM_ERR "eta_conv" "not a eta-redex"
in
fun eta_conv (Abs{Body,...}) = eta_body Body
  | eta_conv (t as Clos _) = eta_conv (push_clos t)
  | eta_conv _ = raise TERM_ERR "eta_conv" "not a eta-redex"
end;


fun inst [] tm = tm
  | inst theta tm =
 let fun inst1 (bv as Bv _) = bv
       | inst1 (c as Const(r,Ty)) =
            (case (Type.ty_sub theta Ty)
               of Type.SAME => c
                | Type.DIFF ty => Const(r, ty))
       | inst1 (v as Fv{Name,Ty}) =
            (case (Type.ty_sub theta Ty)
            of Type.SAME => v
            | Type.DIFF ty => Fv{Name=Name, Ty=ty})
       | inst1 (Comb{Rator,Rand}) =
                Comb{Rator = inst1 Rator, Rand  = inst1 Rand }
       | inst1 (Abs{Bvar,Body}) = Abs{Bvar=inst1 Bvar,Body=inst1 Body}
       | inst1 (t as Clos _) = inst1(push_clos t)
 in
   inst1 tm
 end;


(*---------------------------------------------------------------------------*
 * Matching (first order, modulo aconv) of terms.                            *
 *---------------------------------------------------------------------------*)

val MTM_ERR = TERM_ERR "match_term.tm_reduce" "";

fun seen v tm theta =
  let fun eqv x = (x=v)
  in
   case (Lib.subst_assoc eqv theta)
     of NONE     => false
      | SOME tm' => aconv tm' tm orelse raise MTM_ERR
  end;

local fun free (Bv i) n = i<n
        | free (Comb{Rator,Rand}) n = free Rator n andalso free Rand n
        | free (Abs{Body,...}) n = free Body (n+1)
	| free (t as Clos _) n = free (push_clos t) n
        | free _ _ = true
in
  fun is_free tm = free tm 0
end;

fun tm_reduce (v as Fv{Ty,...}) tm (tm_theta,ty_theta) =
     if (is_free tm)
      then (if (seen v tm tm_theta) then tm_theta else (v |-> tm)::tm_theta,
            Type.type_reduce Ty (type_of tm) ty_theta)
       else raise MTM_ERR
  | tm_reduce (Const(r1, ty1))
                (Const(r2, ty2)) (tm_theta,ty_theta) =
       if (r1=r2)
       then (tm_theta,Type.type_reduce ty1 ty2 ty_theta)
       else raise MTM_ERR
  | tm_reduce (Comb{Rator=M1, Rand=M2})
              (Comb{Rator=N1, Rand=N2}) S = tm_reduce M2 N2 (tm_reduce M1 N1 S)
  | tm_reduce (Abs{Bvar=Fv{Ty=ty1,...}, Body=M})
              (Abs{Bvar=Fv{Ty=ty2,...}, Body=N}) (tm_theta,ty_theta) =
        tm_reduce M N (tm_theta,Type.type_reduce ty1 ty2 ty_theta)
  | tm_reduce (Bv i) (Bv j) S = if (i=j) then S else raise MTM_ERR
  | tm_reduce (pt as Clos _) tm S = tm_reduce (push_clos pt) tm S
  | tm_reduce pt (tm as Clos _) S = tm_reduce pt (push_clos tm) S
  | tm_reduce _ _ _ = raise MTM_ERR;

val term_reduce = tm_reduce


local fun del [] A = A
        | del ((rr as {redex,residue})::rst) A =
           if (redex=residue) then del rst A else del rst (rr::A)
      fun del1 theta =
         let fun delth [] A = A
               | delth ({redex,residue}::rst) A =
                  let val redex' = inst theta redex
                  in if (redex' = residue) then delth rst A
                     else delth rst ((redex' |-> residue)::A)
                  end
         in delth
         end
in
fun match_term pat ob =
   let val (tm_subst,ty_subst) = term_reduce pat ob ([],[])
   in
      (del1 ty_subst tm_subst [], del ty_subst [])
   end
end;


(* Forward reference to Dsyntax. *)
local val dummy = Fv{Name ="dummy",Ty = Type.mk_vartype"'x"}
      val dest_pabs_ref = ref (fn _:term => {varstruct=dummy,body=dummy})
      val dest_pair_ref = ref (fn _:term => {fst=dummy,snd=dummy} )
      val strip_pair_ref = ref (fn _:term => ([]:term list))
      val binder_restr_ref = ref (fn () => ([]:(string*string) list))
      val started = ref false
in
  fun pair_ops f g h i =
    if !started then ()
    else (dest_pabs_ref := f; dest_pair_ref := g;
          strip_pair_ref := h; binder_restr_ref := i; started := true)

  fun d_pabs x = (!dest_pabs_ref) x;
  fun d_pair x = (!dest_pair_ref) x;
  fun s_pair x = (!strip_pair_ref) x;
  fun binder_restrictions() = !binder_restr_ref()
end;

val dot = "."
val comma = ","
val space = " "
val dollar = "$";
val percent = "%";

(*---------------------------------------------------------------------------*
 * A numeral is a nest of NUMERAL_BIT{1,2}s built up from ALT_ZERO wrapped
 * inside the NUMERAL tag, or it is a straight ZERO constant.  This
 * difference in treatment between zero and the other numerals leaves
 * zero as a constant in the logic, which is useful elsewhere.
 * (Principle of least surprises and all that.)  The use of ALT_ZERO rather
 * than ZERO inside the representations for other numerals means that
 * theorems of the form 0 = x will not match inside other numerals.
 *---------------------------------------------------------------------------*)

fun is_numeral t = let

  (* type is equal to ``:num`` *)
  fun is_numtype ty =
     case Type.dest_type ty
      of {Tyop="num", Args=[]} => true
       | _ => false;

  (* type is equal to ``:num -> num`` *)
  fun is_num2num_type ty =
    case Type.dest_type ty
     of {Tyop="fun", Args=[ty1,ty2]} => is_numtype ty1 andalso is_numtype ty2
      | _ => false

  (* term is sequence of applications of NUMERAL_BIT1 and NUMERAL_BIT2 to
     ALT_ZERO *)
  fun is_nb t =
    if is_const t then let
      val {Name, Ty} = dest_const t
    in
      Name = "ALT_ZERO" andalso is_numtype Ty
    end
    else let
      val {Rand, Rator} = dest_comb t
      val {Name, Ty} = dest_const Rator
    in
      (Name = "NUMERAL_BIT1" orelse Name = "NUMERAL_BIT2") andalso
      is_num2num_type Ty andalso is_nb Rand
    end
in
  if is_const t then let
    val {Name, Ty} = dest_const t
  in
    is_numtype Ty andalso Name = "0"
  end
  else let
    val {Rator, Rand} = dest_comb t
    val {Name, Ty} = dest_const Rator
  in
    Name = "NUMERAL" andalso is_num2num_type Ty andalso is_nb Rand
  end handle HOL_ERR _ => false
end

fun dest_numeral t =
  if is_numeral t then
    if is_const t then Arbnum.zero
    else let
      val {Rand = arg, ...} = dest_comb t
      open Arbnum
      fun recurse t =
        if is_comb t then let
          val {Rator, Rand} = dest_comb t
        in
          case #Name(dest_const Rator) of
            "NUMERAL_BIT1" => two * recurse Rand + one
          | "NUMERAL_BIT2" => two * recurse Rand + two
          | _ => raise TERM_ERR "dest_numeral" "This should never ever happen"
        end
        else zero
    in
      recurse arg
    end
  else
    raise TERM_ERR "dest_numeral" "Term is not a numeral"

fun prim_mk_numeral {mkCOMB, mkNUM_CONST, mkNUM2_CONST} n = let
  open Arbnum
  val numeral = mkNUM2_CONST "NUMERAL"
  val nb1 = mkNUM2_CONST "NUMERAL_BIT1"
  val nb2 = mkNUM2_CONST "NUMERAL_BIT2"
  fun recurse x =
    if x = zero then
      mkNUM_CONST "ALT_ZERO"
    else
      if x mod two = one then
        mkCOMB{Rator = nb1, Rand = recurse ((x - one) div two)}
      else
        mkCOMB{Rator = nb2, Rand = recurse ((x - two) div two)}
in
  if n = zero then
    mkNUM_CONST "0"
  else
    mkCOMB{Rator = numeral, Rand = recurse n}
end

fun mk_numeral n = let
  val numtype = Type.mk_type {Tyop = "num", Args = []}
  val num2type = Type.mk_type {Tyop = "fun", Args = [numtype, numtype]}
in
  prim_mk_numeral
  {mkCOMB = mk_comb,
   mkNUM_CONST = (fn s => mk_const {Name = s, Ty = numtype}),
   mkNUM2_CONST = (fn s => mk_const {Name = s, Ty = num2type})} n
end


(* takes a numeral term and turns it into a string *)
val n2i = Arbnum.toString o dest_numeral


(*---------------------------------------------------------------------------*
 *  Raw syntax prettyprinter for terms.                                      *
 *---------------------------------------------------------------------------*)

fun pp_raw_term index pps tm =
let open Portable
    val {add_string,add_break,begin_block,end_block,...} = with_ppstream pps
    fun pr_term (Abs{Bvar,Body}) =
          ( add_string "(\\"; pr_term Bvar; add_string dot;
                              add_break(1,0);  pr_term Body; add_string ")" )
      | pr_term (Comb{Rator, Rand}) =
           ( add_string "("; pr_term Rator; add_break(1,0); pr_term Rand;
             add_string ")" )
      | pr_term (Bv i) = add_string (dollar^Lib.int_to_string i)
      | pr_term a = add_string(percent^Lib.int_to_string (index a))
in
  begin_block INCONSISTENT 0;
  add_string"`"; pr_term (norm_clos tm); add_string"`"; end_block()
end;



(*---------------------------------------------------------------------------*
 * Hidden information sharing between Term and Net. Term nets need to
 * break terms apart when they are accessed, and it is slow to do this
 * by use of dest_abs.
 *---------------------------------------------------------------------------*)
local fun break_abs(Abs{Body,...}) = Body
        | break_abs(t as Clos _) = break_abs (push_clos t)
        | break_abs _ = raise TERM_ERR"hidden.break_abs" "not an abstraction"
      val used = ref false
in
fun Net_init r =
  if !used then () else (r := break_abs; used := true)
end;


(*---------------------------------------------------------------------------*
 * Hidden information sharing between Term and Preterm.                      *
 *---------------------------------------------------------------------------*)
local
  val used = ref false
  fun mk_const0 {Name,Ty} = Const(ref Name, Ty)
in
  fun Preterm_init r1 r2 = if !used then ()
                           else (r1 := mk_const0; r2 := Comb; used := true)
end;


(*---------------------------------------------------------------------------*
 * Hidden information sharing between Term and Theory.                       *
 *---------------------------------------------------------------------------*)
local val used = ref false
      fun break_const(Const x) = x
        | break_const _ = raise TERM_ERR"break_const" ""
in
 fun Theory_init r1 r2 =
      if !used then ()
       else (r1 := Const; r2 := break_const; used := true)
end;


(*---------------------------------------------------------------------------*
 * Hidden information sharing between Term and TheoryPP.                     *
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 * Traverse a term, performing a given (side-effecting) operation at the
 * leaves. For our purposes, bound variables can be ignored.
 *---------------------------------------------------------------------------*)
fun trav f =
  let fun trv (a as Fv _) = f a
        | trv (a as Const _) = f a
        | trv (Comb{Rator, Rand}) = (trv Rator; trv Rand)
        | trv (Abs{Bvar, Body})  = (trv Bvar; trv Body)
        | trv _ = ()
  in
    trv o norm_clos
  end;

local val used = ref false
in
 fun TheoryPP_init r1 = if !used then () else (r1 := trav; used := true)
end;


local val eekr = ref(ref"")
      val used = ref false
in
 fun minTheory_init c =
    if !used then ()
    else case c
           of Const(r,_) => (eekr := r; used := true)
            | _ => raise TERM_ERR"minTheory_init" ""
 fun mk_eq_nocheck ty M N =
  Comb{Rator=Comb{Rator=Const(!eekr,ty-->ty-->Type.bool),Rand=M},Rand=N}
end;

(*---------------------------------------------------------------------------*
 * Hidden information sharing between Term and Thm.                          *
 *---------------------------------------------------------------------------*)

local val used = ref false
in
fun Thm_init r r1 r2 r3 =
   if !used then ()
   else (r := mk_eq_nocheck;
         r1 := Comb; r2 := Abs; r3 := Bv;
         used := true)
end;


end; (* TERM *)
