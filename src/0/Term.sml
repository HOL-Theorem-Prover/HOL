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

fun TY_ANTIQ_ERR s = TERM_ERR s "ty_antiq in term";


(*---------------------------------------------------------------------------*
 * deBruijn terms. ty_antiq is an annoyance, caused by having quotations     *
 * be frag lists. This requires all antiquotes in a quotation to have the    *
 * same type. Thus we use ty_antiq to cast types to terms, in order that all *
 * antiquotes be terms.                                                      *
 *---------------------------------------------------------------------------*)

datatype term = Fv of {Name:string, Ty:Type.hol_type}
              | Bv of int
              | Const of string ref * Type.hol_type
              | Comb of {Rator:term, Rand:term}
              | Abs of {Bvar:term, Body:term}
              | ty_antiq of Type.hol_type;


(* For efficiency tests by Morten Welinder. *)
datatype lambda = VAR   of {Name : string, Ty : Type.hol_type}
                | CONST of {Name : string, Ty : Type.hol_type}
                | COMB  of {Rator : term, Rand : term}
                | LAMB  of {Bvar : term, Body : term};


(*---------------------------------------------------------------------------*
 * Parsing status of constants. This is slightly out of place here; it would *
 * be nice if it was only held in Theory.                                    *
 *---------------------------------------------------------------------------*)
datatype fixity = Infix of int | Prefix | Binder;

fun fixity_to_string(Infix i)  = "Infix "^Lib.int_to_string i
  | fixity_to_string Prefix    = "Prefix"
  | fixity_to_string Binder    = "Binder";


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
  | type_vars_in_term (Bv _) = []
  | type_vars_in_term (ty_antiq _) = raise TY_ANTIQ_ERR "type_vars_in_term";


(*---------------------------------------------------------------------------*
 * The free variables of a lambda term. This could be implemented more       *
 * efficiently, say by an ordered list.                                      *
 *---------------------------------------------------------------------------*)
local
fun frees(v as Fv _) free_list =
      if (mem v free_list) then free_list else v::free_list
  | frees(Comb{Rator, Rand}) free_list = frees Rand (frees Rator free_list)
  | frees(Abs{Body,...}) free_list = frees Body free_list
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
        | frees _ A = A
  in frees tm []
end;


(*---------------------------------------------------------------------------*
 * The *set* of all variables in a term.                                     *
 *---------------------------------------------------------------------------*)
local fun vars (v as Fv _) vlist        = insert v vlist
        | vars(Comb{Rator, Rand}) vlist = vars Rand (vars Rator vlist)
        | vars(Abs{Bvar, Body}) vlist   = vars Body (vars Bvar vlist)
        | vars _ vlist = vlist
in
  fun all_vars tm = vars tm []
end;

fun free_varsl tm_list = itlist (union o free_vars) tm_list []
fun all_varsl tm_list = itlist (union o all_vars) tm_list [];

(*---------------------------------------------------------------------------*
 * Does tm occur free in M. This is not defined modulo aconv. Maybe it       *
 * should be?                                                                *
 *---------------------------------------------------------------------------*)
fun free_in tm M =
   let fun f1 (Comb{Rator,Rand}) = (f2 Rator) orelse (f2 Rand)
         | f1 (Abs{Body,...}) = f2 Body
         | f1 _ = false
       and f2 t = (t=tm) orelse (f1 t)
   in f2 M
   end;


(*---------------------------------------------------------------------------*
 * A total ordering on terms.  Fv < Bv < Const < Comb < Abs                  *
 *---------------------------------------------------------------------------*)

local val TYANTIQ_ERR = TERM_ERR"term_lt" "type antiquotes are not terms"
      fun atom_lt {Name=(s1:string),Ty=ty1}
                  {Name=s2,Ty=ty2}
           = case String.compare (s1,s2)
              of LESS => true
               | EQUAL => Type.type_lt ty1 ty2
               | GREATER => false
in
fun term_lt (ty_antiq _) _ = raise TYANTIQ_ERR
  | term_lt _ (ty_antiq _) = raise TYANTIQ_ERR
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
          {const = Fv{Name="",Ty=Type.mk_vartype"'a"},theory="",place=Prefix})
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

fun prime s = s^"'";

fun primes s =
   let val current = ref s
       fun next () = (current := prime (!current); !current)
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
fun away L init incr =
  let fun vary A [] s = s
        | vary A (h::t) s =
           case String.compare(h,s)
            of LESS => vary A t s
             | EQUAL => vary [] (A@t) (incr())
             | GREATER => vary (h::A) t s
  in
    vary [] L init
  end;

local fun var_name(Fv{Name,...}) = Name
        | var_name _ = raise TERM_ERR "variant.var_name" "not a variable"
in
fun variant [] v = v
  | variant vlist (Fv{Name,Ty}) =
    let val next = nameStrm Name
        val V = map var_name vlist  (* wasteful *)
        fun loop name =
           let val s = away V name next
           in if (inST s) then loop (next()) else s
           end
    in mk_var{Name=loop Name, Ty=Ty}
    end
  | variant _ _ = raise TERM_ERR "variant" "2nd arg. should be a variable"
end;


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
  | mk_comb{Rator,Rand} = list_mk_comb (Rator,[Rand])
                          handle HOL_ERR _ => raise INCOMPAT_TYPES1
end;


(*---------------------------------------------------------------------------*
 * Making abstractions.                                                      *
 *---------------------------------------------------------------------------*)
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

(*---------------------------------------------------------------------------
 * Make a lambda abstraction. Try for some sharing.
 *---------------------------------------------------------------------------*)
fun mk_abs{Bvar as Fv _, Body} =
 let fun bind (v as Fv _) i = if (v=Bvar) then mk_bv(i) else v
       | bind (Comb{Rator,Rand}) i = Comb{Rator=bind Rator i,Rand=bind Rand i}
       | bind (Abs{Bvar=bv, Body=tm}) i = Abs{Bvar = bv, Body = bind tm (i+1)}
       | bind (ty_antiq _) _ = raise TY_ANTIQ_ERR "mk_abs"
       | bind tm _ = tm
 in
   Abs{Bvar = Bvar, Body = bind Body 0}
 end
 | mk_abs _ = raise TERM_ERR "mk_abs" "Bvar not a variable";


fun dest_var (Fv v) = v
  | dest_var _ = raise TERM_ERR "dest_var" "not a var"
fun dest_const (Const (ref name,ty)) = {Name=name,Ty=ty}
  | dest_const _ = raise TERM_ERR"dest_const" "not a const"
fun dest_comb (Comb cmb) = cmb
  | dest_comb _ = raise TERM_ERR "dest_comb" "not a comb"

(*---------------------------------------------------------------------------
 * The pure way to do abstraction destruction. Problem is that you may
 * get a form of variable capture: consider
 *
 *     Abs{Bvar = v, Body = Comb{Rator = Bv 0, Rand = v}}.
 *
 * If you do a dest_abs on this, you will identify Rator and Rand unless
 * you rename. So what? Well, if you don't rename in this situation,
 *
 *   mk_abs o dest_abs <> I
 *
 *
 * fun dest_abs(Abs{Bvar,Body}) =
 *      let fun unbind i (v as (Bv j)) = if (i=j) then Bvar else v
 *            | unbind i (Comb{Rator,Rand}) =
 *                Comb{Rator = unbind i Rator, Rand = unbind i Rand}
 *            | unbind i (Abs{Bvar,Body}) =
 *                Abs{Bvar=Bvar,Body=unbind (i+1) Body}
 *            | unbind _ tm = tm
 *      in
 *      {Bvar = Bvar, Body = unbind 0 Body}
 *      end
 *  | dest_abs _ = raise TERM_ERR{function = "dest_abs",
 *                                message = "not a lambda abstraction"};
 *---------------------------------------------------------------------------*)
local exception CLASH
in
fun dest_abs(Abs{Bvar as Fv{Name,Ty},Body}) =
   let fun dest (v as (Bv j), i) = if (i=j) then Bvar else v
         | dest (v as Fv{Name = s,...}, _) =
               if (Name = s) then raise CLASH else v
         | dest (Comb{Rator,Rand},i) =
              Comb{Rator = dest(Rator,i), Rand = dest(Rand,i)}
         | dest (Abs{Bvar,Body},i) = Abs{Bvar=Bvar,Body = dest(Body,i+1)}
         | dest (tm,_) = tm
   in {Bvar = Bvar, Body = dest(Body,0)}
      handle CLASH =>
      dest_abs(Abs{Bvar = variant (free_vars Body) Bvar, Body = Body})
   end
  | dest_abs _ = raise TERM_ERR "dest_abs" "not a lambda abstraction"
end;

fun dest_ty_antiq (ty_antiq ty) = ty
  | dest_ty_antiq _ = raise TERM_ERR "dest_ty_antiq" "not a type antiquotation"

(*---------------------------------------------------------------------------
 * Discriminators.
 *---------------------------------------------------------------------------*)
fun is_bvar (Bv _)    = true  | is_bvar _  = false;
fun is_var  (Fv _)    = true  | is_var _   = false;
fun is_const(Const _) = true  | is_const _ = false;
fun is_comb (Comb _)  = true  | is_comb _  = false;
fun is_abs  (Abs _)   = true  | is_abs _   = false;

(*---------------------------------------------------------------------------
 * Derived operations
 *---------------------------------------------------------------------------*)
fun rator (Comb{Rator, ...}) = Rator
  | rator _ = raise TERM_ERR "rator" "not a comb"

fun rand (Comb{Rand, ...}) = Rand
  | rand _ = raise TERM_ERR "rand" "not a comb"

val bvar = #Bvar o dest_abs;
val body = #Body o dest_abs;

fun dest_term (Fv a) = VAR a
  | dest_term (Const(ref name,ty)) = CONST{Name=name,Ty=ty}
  | dest_term (Comb r) = COMB r
  | dest_term (a as Abs _) = LAMB(dest_abs a)
  | dest_term _ = raise TERM_ERR "dest_term" "badly formed term"



(*---------------------------------------------------------------------------*
 * fun aconv (Comb{Rator = M1, Rand = M2}) (Comb{Rator=N1,Rand=N2}) =        *
 *          aconv M1 N1 andalso aconv M2 N2                                  *
 *  | aconv (Abs{Bvar=Fv{Ty=ty1,...}, Body = body1})                         *
 *          (Abs{Bvar=Fv{Ty=ty2,...}, Body = body2}) =                       *
 *                         (ty1=ty2) andalso (aconv body1 body2)             *
 *  | aconv tm1 tm2 = (tm1=tm2);                                             *
 *---------------------------------------------------------------------------*)

local fun EQ (M:term,N:term) = Portable.pointer_eq(M,N)
in
fun aconv t1 t2 = EQ(t1,t2) orelse
(case(t1,t2) of
   (Comb{Rator=M,Rand=N},Comb{Rator=P,Rand=Q}) => aconv N Q andalso aconv M P
 | (Abs{Bvar=Fv{Ty=ty1,...}, Body=M},
    Abs{Bvar=Fv{Ty=ty2,...}, Body=N}) => (ty1=ty2) andalso (aconv M N)
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

type binding = {redex : term,
                incoming : {residue:term,
                            fn_residue : string Binaryset.set option ref}};

val empty_string_set = Binaryset.empty String.compare;

local open Binaryset
      fun frees (Fv{Name,...})      FN = add (FN, Name)
        | frees (Comb{Rator, Rand}) FN = frees Rand (frees Rator FN)
        | frees (Abs{Body,...})     FN = frees Body FN
        | frees _ FN = FN
      fun all (Fv{Name,...})      AN = add (AN, Name)
        | all (Comb{Rator, Rand}) AN = all Rand (all Rator AN)
        | all (Abs{Bvar,Body})    AN = all Body (all Bvar AN)
        | all _ AN = AN
in
fun free_names tm = frees tm empty_string_set
fun all_names tm  = all tm empty_string_set
fun vary S init next =
   let fun spin s = if member(S,s) then spin (next()) else s
   in spin init end
end;

(* The numbers of lambdas to go back through. *)
exception CLASH of int;

fun check ([],S) = S
  | check ({redex,residue}::rst, S) =
     if (type_of redex = type_of residue)
     then check(rst,{redex=redex,
                     incoming={residue=residue,
                               fn_residue=ref NONE}}::S)
     else raise TERM_ERR "subst" "redex and residue have different types";

local val incoming_names = ref NONE:string Binaryset.set option ref
      fun opr {residue, fn_residue as ref NONE} =
             let val S = free_names residue
             in fn_residue := SOME S;  S
             end
        | opr {fn_residue = ref (SOME S), ...} = S
in
fun subst [] tm = tm
  | subst theta tm =
    let val bindings = check (theta,[])
        val _ = incoming_names := NONE
        fun mk_incoming() =
             case !incoming_names
              of SOME N => N   (* already computed *)
               | NONE   =>
                  let val N = rev_itlist(fn x => fn S =>
                      Binaryset.union (opr(#incoming x),S))
                         bindings empty_string_set
                  in incoming_names := SOME N;
                      N
                  end
        fun lookup (tm, scope) =
         let fun check_for_clash({residue,...},[]) = SOME residue
               | check_for_clash(rcd as {residue,...},scope) =
                  let val names = opr rcd
                      fun itr ([],_,NONE) = SOME residue
                        | itr ([],_, SOME i) = (mk_incoming();  raise CLASH i)
                        | itr (s::S,n,top) =
                           itr(S, n+1, if Binaryset.member(names,s)
                                       then (SOME n) else top)
                    in  itr(scope,0,NONE)
                    end
             fun assc [] = NONE
               | assc ({redex,incoming}::rst) =
                  if (aconv tm redex)
                  then check_for_clash(incoming,scope)
                  else assc rst
         in
             assc bindings
         end

    fun subs(tm,scope) =
     case lookup(tm,scope)
       of SOME residue => residue
        | NONE => case tm
          of Comb{Rator,Rand} =>
                 Comb{Rator=subs(Rator,scope), Rand=subs(Rand,scope)}
          | Abs{Bvar as Fv{Name,Ty},Body}
              => (Abs{Bvar=Bvar,Body=subs(Body,Name::scope)}
                  handle CLASH 0
                  => let open Binaryset
                         val taken0 = union(all_names Body, mk_incoming())
                         val taken = addList(taken0,scope)
                         val Name' = vary taken Name (nameStrm Name)
                     in
                       Abs{Bvar = Fv{Name=Name',Ty=Ty},
                           Body = subs(Body,Name'::scope)}
                       handle CLASH i => raise CLASH (i-1)
                      (* not due to this abstraction (we just renamed) *)
                     end
                  | CLASH i => raise CLASH(i-1))
          | _ => tm
    in
      subs (tm,[])
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
 * General term substitution without renaming
 *local
 *fun check [] = ()
 *  | check ({redex,residue}::rst) =
 *      if (type_of redex = type_of residue)
 *      then check rst
 *      else raise TERM_ERR{function = "subst",
 *                          message = "redex has different type than residue"}
 *fun aconv_assoc item =
 *   let fun assc ({redex,residue}::rst) =
 *            if (aconv item redex)
 *            then SOME residue
 *            else assc rst
 *         | assc _ = NONE
 *   in assc
 *   end
 *in
 *fun subst [] = Lib.I
 *  | subst s =
 *      let val _ = check s
 *          fun subs tm =
 *             case (aconv_assoc tm s)
 *               of (SOME residue) => residue
 *                | NONE =>
 *                  (case tm
 *                   of (Comb{Rator,Rand}) => Comb{Rator = subs Rator,
 *                                                 Rand = subs Rand}
 *                    | (Abs{Bvar,Body}) => Abs{Bvar = Bvar,
 *                                              Body = subs Body}
 *                    | _ => tm)
 *      in subs
 *      end
 *end;
 *---------------------------------------------------------------------------*)


local val fn_rand = ref NONE
in
fun beta_conv (Comb{Rator = Abs{Body,...}, Rand}) =
 let val _ = fn_rand := NONE
     fun free_rand_names() =
          case !fn_rand
           of SOME S => S
            | NONE => let val S = free_names Rand
                      in  fn_rand := SOME S; S end
     fun check [] = Rand
       | check scope =
            let val names = free_rand_names()
                fun itr([],_,NONE) = Rand
                  | itr ([],_, SOME i) = raise CLASH i
                  | itr (s::S,n,top) =
                     itr(S, n+1, if Binaryset.member(names,s)
                                 then (SOME n) else top)
            in  itr(scope,0,NONE)
            end
     fun subs ((tm as Bv j),i,scope) = if (i=j) then check scope else tm
       | subs (Comb{Rator,Rand},i,scope) =
                Comb{Rator=subs(Rator,i,scope), Rand=subs(Rand,i,scope)}
       | subs (Abs{Bvar as Fv{Name,Ty},Body},i,scope) =
                (Abs{Bvar=Bvar,Body=subs(Body,i+1,Name::scope)}
                 handle CLASH 0
                   => let val taken0 = Binaryset.union
                                         (all_names Body,free_rand_names())
                          val taken = Binaryset.addList(taken0,scope)
                          val Name' = vary taken Name (nameStrm Name)
                      in
                        Abs{Bvar=Fv{Name=Name', Ty=Ty},
                            Body=subs(Body,i+1,Name'::scope)}
                        handle CLASH i => raise CLASH(i-1)
                      end
                 | CLASH i => raise CLASH(i-1))
       | subs (tm,_,_) = tm
 in
   subs (Body,0,[])
 end
| beta_conv _ = raise TERM_ERR "beta_conv" "not a beta-redex"
end;


(*---------------------------------------------------------------------------
 * Non-renaming betaconv.
 * fun beta_conv (Comb{Rator = Abs{Body,...}, Rand}) =
 *   let fun bconv (tm as (Bv j)) i = if (i=j) then Rand else tm
 *         | bconv (Comb{Rator,Rand}) i = Comb{Rator = bconv Rator i,
 *                                             Rand = bconv Rand i}
 *         | bconv (Abs{Bvar,Body}) i = Abs{Bvar=Bvar,Body=bconv Body (i+1)}
 *         | bconv tm _ = tm
 *   in
 *   bconv Body 0
 *   end;
 *---------------------------------------------------------------------------*)

(* Compute lambda to get thrown out to.  *)
fun capture_depth (v,scope) =
   let fun it ([],_) = ~1  (* aka infinity *)
         | it (s::S,n) = if (s=v) then n else it(S, n+1)
   in it(scope,0)
   end;

exception INST_CLASH of {var:term, scope:term list};


fun inst [] tm = tm |
inst theta tm =
 let fun inst1 ((bv as Bv _),_,_) = bv
       | inst1 (c as Const(r,Ty),_,_) =
            (case (Type.ty_sub theta Ty)
               of Type.SAME => c
                | Type.DIFF ty => Const(r, ty))
       | inst1 (v as Fv{Name,Ty},scope1,scope2) =
            let val v' = case (Type.ty_sub theta Ty)
                          of Type.SAME => v
                           | Type.DIFF ty => Fv{Name=Name, Ty=ty}
            in if (capture_depth(v',scope2) = ~1) then v'
               else raise INST_CLASH{var=v', scope=scope2}
            end
       | inst1 (Comb{Rator,Rand},scope1,scope2) =
                Comb{Rator = inst1(Rator,scope1,scope2),
                     Rand  = inst1(Rand,scope1,scope2)}
       | inst1 (Abs{Bvar as Fv{Name,Ty},Body},scope1,scope2) =
            let val v = Fv{Name=Name,Ty=Type.type_subst theta Ty}
                val Bvar' =
                  if (capture_depth(Bvar,scope1)=capture_depth(v,scope2))
                  then v
                  else variant scope2 v
            in Abs{Bvar=Bvar',Body=inst1(Body,Bvar::scope1,Bvar'::scope2)}
                handle e as INST_CLASH{var,scope}
                => if (var = Bvar')
                   then let val Bvar'' = variant (v::scope) Bvar'
                        in
                          Abs{Bvar = Bvar'',
                              Body = inst1(Body,Bvar::scope1,Bvar''::scope2)}
                        end
                   else raise e
            end
       | inst1 (ty_antiq _, _,_) = raise TY_ANTIQ_ERR "inst"
       | inst1 (_, _,_) = raise TERM_ERR "inst.inst1" "badly formed term"
 in
   inst1 (tm,[],[])
 end;


(*---------------------------------------------------------------------------
 * Non renaming version of inst: different from hol88 inst, in that no
 * "away-from" list required
 *local
 *val check : Type.hol_type subst -> bool =
 *    Lib.all (fn {redex,...} => Type.is_vartype redex)
 *in
 *fun inst [] tm = tm
 *  | inst theta tm =
 *     if (check theta)
 *     then let fun inst1 (Fv{Name,Ty}) = Fv{Name=Name,
 *                                           Ty = Type.type_subst theta Ty}
 *                | inst1 (Const{Name,Ty}) = Const{Name=Name,
 *                                                 Ty=Type.type_subst theta Ty}
 *                | inst1 (Comb{Rator,Rand}) = Comb{Rator = inst1 Rator,
 *                                                  Rand = inst1 Rand}
 *                | inst1 (Abs{Bvar,Body}) = Abs{Bvar = inst1 Bvar,
 *                                               Body = inst1 Body}
 *                | inst1 (bv as Bv _) = bv
 *                | inst1 (ty_antiq _) = raise TY_ANTIQ_ERR "inst"
 *          in
 *          inst1 tm
 *          end
 *     else raise TERM_ERR{function = "inst",
 *			 message = "redex in type substitution not a variable"}
 *end;
 *---------------------------------------------------------------------------*)


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
  | tm_reduce _ _ _ = raise MTM_ERR;


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
   let val (tm_subst,ty_subst) = tm_reduce pat ob ([],[])
   in
      (del1 ty_subst tm_subst [], del ty_subst [])
   end
end;



(******************* Term Pretty Printer ************************************)
open Portable_PrettyPrint;

type gravity = gravity
type pparg = {boundvars:term list,depth:int,gravity:gravity}
                -> term -> ppstream -> unit

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

(*---------------------------------------------------------------------------
 * alphanumeric binders have a space between them and the variable:
 * otherwise we get the following buggy prettyprint reported by Paul
 * Curzon (LOCAL is a binder)
 *
 *     LOCALx. <body>
 *---------------------------------------------------------------------------*)
fun pad_binder s = if (Lexis.ok_symbolic s) then s else s^space;


(*--------------------- Breaking terms down --------------------------------*)

(*---------------------------------------------------------------------------
 * Strips leading lambdas off a term, not bothering to adjust indices
 *---------------------------------------------------------------------------*)
fun de_abs (Abs{Bvar,Body}) =
        let val (bvs, core) = de_abs Body
        in (Bvar::bvs, core)
        end
  | de_abs tm = ([],tm);


local fun strip (Comb{Rator=Const(ref "~",_), Rand}) n = strip Rand (n+1)
        | strip tm n = (n,tm)
in
fun strip_neg tm = strip tm 0
end;

fun name_of (ref s,_) = s;

fun fixity_of s = #place(const_decl s) handle HOL_ERR _ => Prefix;

fun is_binder s = (fixity_of s = Binder)
fun is_infix s = (case (fixity_of s) of Infix _ => true | _ => false)
fun prec_of s = (case (fixity_of s) of Infix i => i | _ => 0)

local fun dest (tm as Comb{Rator = Const c, Rand = Abs{Bvar,Body}}) s L =
           if (name_of c = s) then dest Body s (Bvar::L) else (rev L,tm)
        | dest tm _ L = (rev L,tm)
in
fun strip_binder_vars (tm as Comb{Rator=Const c,Rand=Abs{Bvar,Body}}) =
     let val Name = name_of c
     in if (is_binder Name) then dest Body Name [Bvar] else ([],tm)  end
  | strip_binder_vars tm = ([],tm)
end;


fun strip_list (M as Comb{Rator=Comb{Rator=Const c, Rand=t1}, Rand=t2}) L =
     if (name_of c = "CONS") then strip_list t2 (t1::L) else M::L
  | strip_list tm L = (tm::L);

fun is_infixed_comb (Comb{Rator=Comb{Rator=Const c,...},...}) =
      is_infix (name_of c)
  | is_infixed_comb _ = false;


fun strip_infix(tm as Comb{Rator=Comb{Rator=Const c,Rand=t1},Rand=t2}) =
  let val Name = name_of c
     fun dest (tm as Comb{Rator=Comb{Rator=Const(ref s,_),Rand=t1},
                          Rand = t2}) L =
                 if (Name = s) then dest t2 (t1::L) else rev (tm::L)
           | dest tm L = rev (tm::L)
     in if (is_infix Name) then dest t2 [t1] else [tm] end
  | strip_infix tm = [tm];



(*---------------------------------------------------------------------------
 * First clause corresponds to GSPEC (\v. (M,N)) ;
 *  second to GSPEC (\(v1,...,vn).(M,N))
 *---------------------------------------------------------------------------*)
exception NOT_SET_ABS;

fun strip_set_abs(tm as Abs _) =
    let val {Bvar,Body} = dest_abs tm
    in case Body
         of Comb{Rator=Comb{Rator=Const c,Rand=tm1},Rand=tm2} =>
              if (name_of c = ",")
              then if ([Bvar] = intersect (free_vars tm1) (free_vars tm2))
                   then ([Bvar],tm1,tm2) else raise NOT_SET_ABS
              else raise TERM_ERR"strip_set_abs" "badly formed set abstraction"
          | _ => raise TERM_ERR"strip_set_abs" "badly formed set abstraction"
    end
  | strip_set_abs tm =
      let val {varstruct, body} = d_pabs tm
          val L = s_pair varstruct
          val {fst,snd} = d_pair body
      in
        if (set_eq L (intersect (free_vars fst) (free_vars snd)))
        then (L,fst,snd)
        else raise NOT_SET_ABS
      end
      handle HOL_ERR _ => raise NOT_SET_ABS;




(*---------------------------------------------------------------------------
 * Printing functions for variables. Bound variables need to be looked up in
 *  the environment E to get their info (name and type).
 *---------------------------------------------------------------------------*)
local fun lookup 0 (Fv x::_) = x
        | lookup n (_::rst) = lookup (n-1) rst
        | lookup _ _ = raise TERM_ERR "pr_var" "lookup"
in
fun pr_var ppstrm =
   let val add_string = add_string ppstrm
       fun pr_atom 0 _ _ = add_string " ... "
	 | pr_atom n {Name,Ty} showtype =
             if (showtype)
             then ( add_string ("("^Name^" :");
                    Type.pp_type ppstrm Ty (n-1);
                    add_string ")"
                  )
             else add_string Name
       fun pr_v 0 _ _ = add_string " ... "
         | pr_v n _ (Fv v) = pr_atom n v (!Globals.show_types)
         | pr_v n E (Bv i) =
              if (!Globals.show_dB)
              then add_string ("("^Lib.int_to_string i^")")
              else pr_atom n (lookup i E) false
         | pr_v _ _ _ = raise TERM_ERR "pr_var" "not a var"
   in   pr_v
   end
fun pr_var_list ppstrm n =
   pr_list_to_ppstream ppstrm
      (fn ppstrm => pr_var ppstrm n [])
      (fn _ => ())
      (fn ppstrm => add_break ppstrm (1,0))
end;



(*---------------------------------------------------------------------------
 * Varstructs are odious. I found that the easiest way to handle them
 * is to map them to (perhaps partial) s-expressions.
 *---------------------------------------------------------------------------*)
datatype sexp = premature_end
              | atom of term
              | unc of (sexp*sexp);

(*---------------------------------------------------------------------------
 * Map to <sexp,term,env> triple. Takes a term and returns the first
 * varstruct (mapped to an sexp), the rest of the term, and the env arising
 * from the first varstruct.
 *---------------------------------------------------------------------------*)
fun dest_uncurry (Abs{Bvar,Body}) = (atom Bvar, Body,[Bvar])
  | dest_uncurry (M as Comb{Rator = Const c, Rand}) =
     if (name_of c =  "UNCURRY")
     then let val (s,M,e0) = dest_uncurry Rand
              val (t,N,e1) = dest_uncurry M
          in
            (unc(s,t), N, (e1@e0))
          end
     else (premature_end,M,[])
  | dest_uncurry M = (premature_end,M,[]);


(* Get top level tuple from sexp *)
fun get_backbone (unc(M,N)) = M::(get_backbone N)
  | get_backbone x = [x];


(*---------------------------------------------------------------------------
 * Takes an sexp and prints it. Therefore, this will print one element from
 * a varstruct list.
 *---------------------------------------------------------------------------*)
fun pr_varstruct ppstrm =
   let val {add_string,add_break,begin_block,end_block,...} =
              with_ppstream ppstrm
       val pr_var = pr_var ppstrm
       fun pr_infix_unc L n =
           ( begin_block INCONSISTENT 2;
             add_string "(";
             pr_list
               (pr_vstruct n)
               (fn () => add_string ",")
               (fn () => add_break(0,0))  L;
             add_string ")";
             end_block())
       and
           pr_vstruct n (S as unc _) = pr_infix_unc (get_backbone S) n
         | pr_vstruct n (atom (v as Fv _)) = pr_var n [] v
         | pr_vstruct _ premature_end =
	   raise TERM_ERR "pr_vstruct" "premature end"
         | pr_vstruct _ (atom _) =
	       raise TERM_ERR "pr_vstruct" "badly formed varstruct"
   in   pr_vstruct
   end;

(*---------------------------------------------------------------------------
 * Strips a term of parse form "\<varstruct_list>.M" into a triple:
 * <funcs,term,env>. Each member f in funcs has type (unit -> unit).
 * Each f either prints out a list of variables (using pr_var_list)
 * or a single, complete varstruct (using pr_varstruct).
 *---------------------------------------------------------------------------*)
fun strip_varstruct ppstrm =
 let val pvstruct = pr_varstruct ppstrm
     val pvlist = pr_var_list ppstrm
     fun strip (tm as Comb{Rator = Const c,...}) =
          if (name_of c = "UNCURRY")
          then let val (s,M,e0) = dest_uncurry tm
               in if (hd(rev(get_backbone s)) = premature_end)
                  then ([],tm,[])
                  else let val (L,M',e1) = strip M
                       in ((fn n => pvstruct n s)::L, M', e1@e0)
                       end
               end
          else ([],tm,[])
       | strip (tm as Abs _) =
          let val (V,M) = de_abs tm
              val (L,M',e) = strip M
          in ((fn n => pvlist n V)::L, M', (e@rev V))
          end
       | strip tm = ([],tm,[])
 in
   strip
 end;

(*---------------------------------------------------------------------------
 * "bump" is used in stripping restricted quantifiers. It increments the
 * index of any bound variables inside a restriction. This is used in the case
 *
 *     RQ <pred1> (\x. RQ <pred2> (\y. M))
 *
 * where RQ is a restricted quantifier constant. If pred1 and pred2 are the
 * same, then we want to print
 *
 *     RQ x y ::<pred1>. M
 *
 * but if not then we print
 *
 *     RQ x::<pred1>. RQ y::pred2. M
 *
 * The problem comes with testing that pred1 and pred2 are the same. We
 * test up to alpha-convertibility, but we can't just check the dB structure,
 * since pred2 is one binder "past" pred1.
 *
 * Example.
 *
 *     - %`!x y. !a::($> x). !b::($> y). (x > y) ==> (a > b)`;
 *     val it = (--`!x y. !a b ::($> x). x > y ==> a > b`--) : term
 *
 * Showing the dB structure and the restricted quantifiers, this is
 *
 *     - %`!x y. !a::($> x). !b::($> y). (x > y) ==> (a > b)`;
 *     val it =
 *     `!x y. RES_FORALL ($> (1))
 *            (\a. RES_FORALL ($> (1)) (\b. (3) > (2) ==> (1) > (0)))`
 *
 * Notice that the "x" in "($> x)" is one away from its binder, as is the
 * "y" in "($> y)". Hence, just testing with aconv will not be correct.
 *
 *---------------------------------------------------------------------------*)

fun bump (Bv i) = Bv (i+1)
  | bump (Comb{Rator,Rand}) = Comb{Rator=bump Rator, Rand=bump Rand}
  | bump (Abs{Bvar,Body}) = Abs{Bvar=Bvar,Body=bump Body}
  | bump x = x;

fun strip_restr_quant ppstrm {binder,restr,rest} =
 let val pvstruct = pr_varstruct ppstrm
     val pvar = pr_var ppstrm
     fun strip R (tm as Comb{Rator = Const c,...}) =
           if (name_of c = "UNCURRY")
           then let val (s,M,e0) = dest_uncurry tm
                in if (hd(rev(get_backbone s)) = premature_end)
                   then ([],tm,[])
                   else let val (L,M',e1) = strip_next (bump R) M
                        in ((fn n => pvstruct n s)::L, M', e1@e0)
                        end
                end
           else ([],tm,[])
       | strip R (Abs{Bvar,Body}) =
           let val (L,Body',e) = strip_next (bump R) Body
           in ((fn n => pvar n [] Bvar)::L, Body', (e@[Bvar]))
           end
       | strip _ tm = ([],tm,[])
     and strip_next R (tm as Comb{Rator=Comb{Rator=Const c,Rand=rstn}, Rand}) =
           if (name_of c = binder andalso (aconv rstn R)) then strip R Rand
           else ([],tm,[])
       | strip_next _ tm = ([],tm,[])
 in
   strip restr rest
 end;


fun strip_let ppstrm =
 let fun strip (M as Comb{Rator=Comb{Rator=Const c,Rand=A1},Rand=A2}) =
   if (name_of c <> "LET") then ([],M,[])
   else (case A1
    of Abs{Bvar,Body} => ([((fn n => pr_var ppstrm n [] Bvar),A2)],Body,[Bvar])
     | Comb{Rator=Const c,...} =>
         if (name_of c = "UNCURRY")
         then let val (s,tm2,e) = dest_uncurry A1
              in if (hd(rev(get_backbone s)) = premature_end) then ([],M,[])
                 else ([((fn n => pr_varstruct ppstrm n s),A2)],tm2,e)
              end
         else blat (M,A1,A2)
     | _ => blat (M,A1,A2))
 | strip M = ([],M,[])
and
 blat (M,tm1,tm2) =
  case (strip tm1)
    of (L,Abs{Bvar,Body},e) =>
         (((fn n => pr_var ppstrm n [] Bvar),tm2)::L,Body, Bvar::e)
     | (L, tm as Comb{Rator = Const c,...},e0) =>
         if (name_of c = "UNCURRY")
         then let val (s,tm3,e1) = dest_uncurry tm
              in if (hd(rev(get_backbone s)) = premature_end)
                 then (L,tm,e0)
                 else (((fn n => pr_varstruct ppstrm n s),tm2)::L,tm3,(e1@e0))
          end
          else ([],M,[])
     | _ => ([],M,[])
 in
  strip
 end;

(*---------------------------------------------------------------------------
 * How should a constant name be printed? Here it is hardwired, but we should
 * actually leave it up to the user. Some of the cases to consider are:
 *
 *   A. If we are printing a constant that is really a binder or an infix,
 *      then we should "dollar" it.
 *
 *   B. If the constant is not in the symbol table, then it can be one of two
 *      things: a member of a constant family, or an overwritten constant.
 *      if the latter, we should tell the user that the constant is out of
 *      date by printing some funny syntax around the name.
 *
 *   C. What about overwritten constant families? A member of a constant
 *      family is considered to be overwritten if its type has been
 *      overwritten.
 *---------------------------------------------------------------------------*)
datatype dollared = maybe | no
fun old s = !Globals.old s;
fun unknown s = String.concat["unknown->",s,"<-unknown"];

fun trans_name ("NIL", "list",_,_)      = "[]"
  | trans_name ("NIL", _, _,_)          = "NIL"
  | trans_name ("EMPTY","set",_,_)      = "{}"
  | trans_name ("EMPTY","pred_set",_,_) = "{}"
  | trans_name ("EMPTY",_,_,_)          = "EMPTY"
  | trans_name ("emptystring",_,_,_)    = "\"\""
  | trans_name ("ZERO",_,_,_)           = "0"
  | trans_name (name,_,Prefix,_)        = name
  | trans_name (name,_,_,no)            = name
  | trans_name (name,_,_,maybe)         = dollar^name;

fun cname ((r as ref name),ty) d =
  let val {const=Const(r1,_),theory,place} = const_decl name
      val cstr = trans_name (name,theory,place,d)
  in
    if (r = r1) then cstr else old name
  end handle HOL_ERR _ => old name


fun listCONS ty =
  let val (x,y) = Type.dom_rng (snd (Type.dom_rng ty))
  in case (Type.dest_type x)
      of {Tyop="list",Args=[_]} => (x=y)
       | _ => raise TERM_ERR "" ""
  end
  handle HOL_ERR _ => false;

fun is_pred_ty ty =
  (case Type.dest_type (snd(Type.dom_rng ty))
    of {Tyop="bool",Args=[]} => true
    | _ => false)
  handle HOL_ERR _ => false;

fun is_set_ty ty =
  (case (Type.dest_type ty) of {Tyop="set",...} => true | _ => false)
  handle HOL_ERR _ => false;

fun setINSERT ty =
  let val hty = snd(Type.dom_rng(snd(Type.dom_rng ty)))
  in
   is_pred_ty hty orelse is_set_ty hty
  end handle HOL_ERR _ => false;

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
  fun is_numtype ty = let
    val {Tyop, Args} = Type.dest_type ty
  in
    Tyop = "num" andalso null Args
  end handle HOL_ERR _ => false

  (* type is equal to ``:num -> num`` *)
  fun is_num2num_type ty = let
    val {Tyop, Args} = Type.dest_type ty
  in
    Tyop = "fun" andalso length Args = 2 andalso List.all is_numtype Args
  end handle HOL_ERR _ => false

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
    is_numtype Ty andalso Name = "ZERO"
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
    if is_const t then arbnum.zero
    else let
      val {Rand = arg, ...} = dest_comb t
      open arbnum
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
  open arbnum
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
    mkNUM_CONST "ZERO"
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
val n2i = arbnum.toString o dest_numeral


(*---------------------------------------------------------------------------*
 *                                                                           *
 *             The term pretty printer                                       *
 *                                                                           *
 *---------------------------------------------------------------------------*)


local

val pp_tm_ref : (ppstream -> term -> gravity -> term list -> int -> unit) ref
    = ref (fn _ => fn _ => fn _ => fn _ => fn _ => ())

fun initial_pp_tm ppstrm =
   let val {add_string,add_break,begin_block,end_block,add_newline,...} =
              with_ppstream ppstrm
       val pr_var = pr_var ppstrm
       val pr_var_list = pr_var_list ppstrm
       val pr_varstruct = pr_varstruct ppstrm
       val strip_varstruct = strip_varstruct ppstrm
       val add_lparen = add_lparen ppstrm
       val add_rparen = add_rparen ppstrm
       val pp_type = Type.pp_type ppstrm
       fun pr_const (p as (_,ty)) n d =
          let val ptype = !Globals.show_types
          in if ptype then add_string "(" else ();
             add_string (cname p d);
             if ptype
             (* maybe (add_break(1,0);BB;add_string":";pp_type;EB  ... *)
             then (add_string " :"; pp_type ty (n-1); add_string ")")
             else ()
          end
       fun pr_term_hook tm grav E n = (!pp_tm_ref) ppstrm tm grav E n

fun pr_comb rator rand grav E n =
   (begin_block (if (!(#stack_infixes(Globals.pp_flags)))
                 then CONSISTENT else INCONSISTENT) 2;
     add_lparen grav APPL;
     if (is_infixed_comb rator)  (* to print `(f o g) x` properly *)
     then pr_term_hook rator APPL E (n-1)
     else pr_term_hook rator WEAK E (n-1);
     add_break(1,0);
     pr_term_hook rand APPL E (n-1);
     add_rparen grav APPL;
     end_block ())
and
pr_infix s p L grav E n =
   let val prec = INFIX p
   in add_lparen grav prec;
      begin_block (if (!(#stack_infixes(Globals.pp_flags))) then CONSISTENT
                   else INCONSISTENT) 0;
      (*---------------------------------------------------------------------*
       * if infix_at_front and we're printing A /\ B, we have the            *
       * following stream: A <BR> "/\ " B                                    *
       * otherwise: A " /\" <BR> B                                           *
       *---------------------------------------------------------------------*)
      pr_list
        (fn trm => pr_term_hook trm prec E (n-1))
        (fn () => if (!(#infix_at_front(Globals.pp_flags)))
                  then add_break(if(s<>comma) then 1 else 0,0)
                  else add_string((if(s<>comma)then space else"")^s))
        (fn () => if (!(#infix_at_front(Globals.pp_flags)))
                  then add_string(s^space)
                  else add_break(if (s<>comma) then 1 else 0,0)) L;
      end_block();
      add_rparen grav prec
   end
and
(*---------------------------------------------------------------------------
 * The pattern match for pr_term goes like this (c stands for a Const):
 *
 *     Fv       (* free variable *)
 *     Bv       (* bound variable *)
 *     Const    (* constant *)
 *     Abs      (* lambda abstraction *)
 *     c P Q R  (* c = COND *)
 *     c P Q    (* c = {CONS, INSERT, LET, <infix>, <restricted binder>} *)
 *     c P      (* c = {~, GSPEC, UNCURRY, <binder>, <binder> <vstruct>} *)
 *     P Q      (* fall through case for Combs *)
 *     ty_antiq (* injection of hol_type into term, so have to cater for it. *)
 *
 *---------------------------------------------------------------------------*)
    pr_term _ _ _ 0 = add_string " ... "
  | pr_term (v as Fv _) grav E n = pr_var n E v
  | pr_term (v as Bv _) grav E n = pr_var n E v
  | pr_term (c as Const p) _ _ n = pr_const p n maybe
  | pr_term (tm as Abs _) grav E n =         (* simple abstractions *)
           let val (F,body,e) = strip_varstruct tm
           in
             begin_block CONSISTENT 2;
             add_lparen grav WEAK;
             add_string "\\";
               begin_block INCONSISTENT 1;
               pr_list
                   (fn f => f n)
                   (fn () => ())
                   (fn () => add_break(1,0))  F;
               end_block();
             add_string ".";
             add_break(1,0);
               begin_block INCONSISTENT 2;
               pr_term_hook body BOTTOM (e@E) (n-1);
               end_block();
             add_rparen grav WEAK;
             end_block()
           end

    (*-----------------------------------------------------------------------
     * conditionals, the only 3 argument built in constant recognized by
     * pr_term
     *-----------------------------------------------------------------------*)
  | pr_term (Comb{Rator=Comb{Rator=Comb{Rator=Const(ref"COND",_),Rand=b},
                             Rand = larm}, Rand = rarm}) grav E n =
           ( add_lparen grav WEAK;
             begin_block CONSISTENT 0;
             pr_term_hook b TOP E (n-1);
             add_break(1,0);
             add_string "=> ";
             pr_term_hook larm TOP E (n-1);
             add_break(1,0);
             add_string "| ";
             pr_term_hook rarm TOP E (n-1);
             end_block();
             add_rparen grav WEAK
           )

    (*-----------------------------------------------------------------------
     * 2 argument specially handled constants: CONS, INSERT, LET, all
     * infixes, and restricted quantifiers.
     *-----------------------------------------------------------------------*)

    (* lists *)
  | pr_term (tm as Comb
        {Rator=f as Comb{Rator=Const(ref "CONS",Ty),...}, Rand}) grav E n =
     if (listCONS Ty)
     then let val l = strip_list tm []
         in
          case (Portable_List.hd l)
             of Const(ref"NIL",_) =>
                    ( begin_block INCONSISTENT 1;
                      add_string "[";
                      pr_list
                          (fn trm => pr_term_hook trm BOTTOM E (n-1))
                          (fn () => add_string ";")
                          (fn () => add_break(1,0))
                          (Portable_List.rev (Portable_List.tl l));
                      add_string "]";
                      end_block() )
              | _ => pr_comb f Rand grav E n
         end
      else pr_comb f Rand grav E n
    (*----------------------------------------------------------------------
     * enumerated set
     *-----------------------------------------------------------------------*)
  | pr_term(tm as Comb{Rator=Comb{Rator=Const(ref"INSERT",ty),...},...})
      grav E n =
       if (setINSERT ty)
       then let val L = strip_infix tm
                val (front,last) = Lib.front_last L
                val p = prec_of "INSERT"
           in case last
              of Const(ref"EMPTY",_) =>
                  ( begin_block INCONSISTENT 1;
                    add_string "{";
                    Portable_PrettyPrint.pr_list
                         (fn trm => pr_term_hook trm BOTTOM E (n-1))
                               (fn () => add_string ";")
                               (fn () => add_break(1,0))   front;
                    add_string "}"; end_block())
              | _ => pr_infix "INSERT" p L grav E n
           end
       else pr_comb (rator tm) (rand tm) grav E n
    (*-----------------------------------------------------------------------
     * let statements
     *-----------------------------------------------------------------------*)
  | pr_term (tm as Comb{Rator as Comb{Rator=Const(ref"LET",_),...}, Rand})
            grav E n =
     (case (strip_let ppstrm tm)
      of ([],_,[]) => pr_comb Rator Rand grav E n
       | ([],_,_) => raise TERM_ERR "pr_term" "let clause"
       | (L,m,e) =>
         let fun pr_and_binds (s,(f,arg)) =  (* s = "let" or "and" *)
              let val (F,body,e') = strip_varstruct arg
              in begin_block INCONSISTENT 2;
                   add_string s; add_break(1,0);
                   f n;  (* print let-bound name *)
                   if (null F)  (* args *) then () else add_string " ";
                   pr_list (fn f => f n) (fn () => ())
                           (fn () => add_break(1,0))   F;
                   add_string " ="; add_break(1,2);
                 pr_term_hook body WEAK (e'@E) (n-1);
                 end_block()
              end
              (* Ad hoc, ad hoc, ad hoc *)
              fun rev1 ([],A) = A
                | rev1 ([p],A) = ("let",p)::A
                | rev1 (p::rst,A) = rev1(rst,("and",p)::A)
         in
           add_lparen grav WEAK;
           begin_block CONSISTENT 0;
           if !Globals.in_at_end then begin_block CONSISTENT 0 else ();
           begin_block CONSISTENT 0;
               pr_list pr_and_binds
                  (fn () => ()) (fn () => add_break(1,0))
                  (rev1(L,[]));  end_block();
           add_break(1,0);
           add_string "in";
           if !Globals.in_at_end then end_block() else ();
           add_break(1,0);
           pr_term_hook m BOTTOM (e@E) (n-1);  (* pp the body *)
           end_block();
           add_rparen grav WEAK
         end)

    (*-----------------------------------------------------------------------
     * "infix" case and restricted quantifier case
     *-----------------------------------------------------------------------*)
  | pr_term (tm as Comb{Rator as Comb{Rator=Const (cr as (ref name,_)),
                                      Rand = t1},
                        Rand}) grav E n =
      (case (fixity_of name)
       of Infix p => pr_infix (cname cr no) p (strip_infix tm) grav E n
       |       _  => (* decide if name is that of a restricted binder *)
         if not(!Globals.show_restrict) then pr_comb Rator Rand grav E n
        else
       (case (Lib.assoc2 name (binder_restrictions()))
        of NONE => pr_comb Rator Rand grav E n  (* not a restr. quantifier *)
         | SOME (binder,_) =>
           (case (strip_restr_quant ppstrm {binder=name,restr=t1,rest=Rand})
            of ([],_,_) => pr_comb Rator Rand grav E n
             | (F,body,e) =>
               ( begin_block CONSISTENT 2;
                 add_lparen grav WEAK;
                 add_string (pad_binder binder);
                 begin_block INCONSISTENT 1;
                 pr_list (fn f => f n) (fn () => ())
                         (fn () => add_break(1,0))  F;
                 add_break (1,0);
                 add_string "::"; add_break (0,0);
                 pr_term_hook t1 APPL E (n-1);
                 end_block();
                 add_string "."; add_break(1,0);
                 begin_block INCONSISTENT 2;
                 pr_term_hook body BOTTOM (e@E) (n-1);
                 end_block();
                 add_rparen grav WEAK;
                 end_block()))))

    (*-----------------------------------------------------------------------
     * Built in constants taking one argument : negation ("~"), GSPEC,
     * UNCURRY, <binder>, <binder> <vstruct>
     *-----------------------------------------------------------------------*)
    (* negations *)
  | pr_term (tm as Comb{Rator = Const(ref"~",_), ...}) grav E d =
      let val (n,m) = strip_neg tm
      in add_lparen grav APPL;
         Lib.for_se 0 (n-1) (fn _ => add_string "~");
         pr_term_hook m APPL E (d-1);
         add_rparen grav APPL
      end

    (*-----------------------------------------------------------------------
     * set abstractions
     *-----------------------------------------------------------------------*)
  | pr_term (Comb{Rator as Const(ref"GSPEC",_), Rand}) grav E n =
      ( let val (e,tm1,tm2) = strip_set_abs Rand
            val e' = e@E
        in
          begin_block CONSISTENT 2;
          add_string "{";
          pr_term_hook tm1 BOTTOM e' (n-1);
          add_string " |"; add_break (1,0);
          pr_term_hook tm2 BOTTOM e' (n-1);
          add_string "}";
          end_block()
        end handle NOT_SET_ABS => pr_comb Rator Rand grav E n )

    (*-----------------------------------------------------------------------
     * lambda varstructs:  \(x,y). M
     *-----------------------------------------------------------------------*)
  | pr_term (tm as Comb{Rator as Const(ref"UNCURRY",_),Rand}) grav E n =
     (case (strip_varstruct tm)
      of ([],_,_) => pr_comb Rator Rand grav E n
       | (F,body,e) =>
         ( begin_block CONSISTENT 2;
           add_lparen grav WEAK;
           add_string "\\";
           begin_block INCONSISTENT 1;
           pr_list (fn f => f (n-1)) (fn () => ())
                   (fn () => add_break(1,0))    F;
           end_block();
           add_string "."; add_break(1,0);
           begin_block INCONSISTENT 2;
           pr_term_hook body BOTTOM (e@E) (n-1);
           end_block();
           add_rparen grav WEAK;
          end_block()))

    (*----------------------------------------------------------------------
     *  binder applied to varstruct: e.g.,  !(x,y,z). M
     *----------------------------------------------------------------------*)
  | pr_term (Comb{Rator as Const(cr as (ref cstr,_)),
                  Rand as Comb{Rator = Const(ref"UNCURRY",_),...}})
              grav E n =
      if (fixity_of cstr <> Binder) then pr_comb Rator Rand grav E n
      else (case (strip_varstruct Rand)
            of ([],_,_) => pr_comb Rator Rand grav E n
             | (F,body,e) =>
               (begin_block CONSISTENT 2;
                add_lparen grav WEAK;
                add_string (pad_binder (cname cr no));
                begin_block INCONSISTENT 1;
                pr_list (fn f => f (n-1)) (fn () => ())
                        (fn () => add_break(1,0))    F;
                end_block();
                add_string "."; add_break(1,0);
                begin_block INCONSISTENT 2;
                pr_term_hook body BOTTOM (e@E) (n-1);
                end_block();
                add_rparen grav WEAK;
                end_block()))

    (*-----------------------------------------------------------------------
     * "binder" case: e.g. !x y z. M.
     *-----------------------------------------------------------------------*)
  | pr_term (trm as Comb{Rator=c as Const(cr as (ref name,_)),Rand=tm as Abs _})
            grav E n =
      if (fixity_of name <> Binder)
      then pr_comb c tm grav E n
      else let val (V,body) = strip_binder_vars trm
           in begin_block INCONSISTENT 2;
              add_lparen grav WEAK;
              begin_block INCONSISTENT 1;
              add_string (pad_binder (cname cr no));
              pr_var_list (n-1) V;
              end_block();
              add_string "."; add_break(1,0);
              pr_term_hook body BOTTOM (rev V@E) (n-1);
              add_rparen grav WEAK;
              end_block()
           end

  (*-----------------------------------------------------------------------*
   * Numeral case.                                                         *
   *-----------------------------------------------------------------------*)
  | pr_term (tm as Comb{Rator as Const(ref"NUMERAL", _), Rand}) grav E n = (let
      val nstr = n2i tm
    in
      if !Globals.show_types then add_string "(" else ();
      add_string (n2i tm);
      if !Globals.show_types then
        (add_string " :"; pp_type (type_of Rand) (n-1); add_string ")")
      else ()
    end handle _ => pr_comb Rator Rand grav E n)


  (*------------------------------------------------------------------------
   * fall through case for combs
   *-------------------------------------------------------------------------*)
  | pr_term (Comb{Rator, Rand}) grav E n = pr_comb Rator Rand grav E n

  | pr_term (ty_antiq ty) grav E n =
     (begin_block CONSISTENT 0;
      add_string ("(ty_antiq("^(!Globals.type_pp_prefix)^"`:");
      pp_type ty (n-1);
      add_string ("`"^(!Globals.type_pp_suffix)^"))");
      end_block())

in  pr_term
end;

val _ = pp_tm_ref := initial_pp_tm;

in

fun pp_tm ppstrm tm grav E n = (!pp_tm_ref) ppstrm tm grav E n;

fun extend_pp_term print_fun =
   let val old_pp_tm = !pp_tm_ref
       fun new_pp_tm ppstrm tm grav E n =
          let fun pp_tm {boundvars,depth,gravity} tm ppstrm =
                 (!pp_tm_ref) ppstrm tm gravity boundvars depth
          in  (print_fun pp_tm {boundvars=E,depth=n,gravity=grav} tm ppstrm)
              handle HOL_ERR _ => (old_pp_tm ppstrm tm grav E n)
          end
   in  pp_tm_ref := new_pp_tm
   end;

fun reset_pp_term () = (pp_tm_ref := initial_pp_tm);

end;

fun pp_term ppstrm tm =
   if (!Globals.max_print_depth = 0)
   then Portable_PrettyPrint.add_string ppstrm " ... "
   else pp_tm ppstrm tm BOTTOM [] (!Globals.max_print_depth);


(*---------------------------------------------------------------------------*
 *  Raw syntax prettyprinter for terms.                                      *
 *---------------------------------------------------------------------------*)

fun pp_raw_term index pps tm =
let val {add_string,add_break,begin_block,end_block,...} = with_ppstream pps
    fun pr_term (Abs{Bvar,Body}) =
          ( add_string "(\\"; pr_term Bvar; add_string dot;
                              add_break(1,0);  pr_term Body; add_string ")" )
      | pr_term (Comb{Rator, Rand}) =
           ( add_string "("; pr_term Rator; add_break(1,0); pr_term Rand;
             add_string ")" )
      | pr_term (ty_antiq _) = raise TERM_ERR"pp_raw_term" "term construction"
      | pr_term (Bv i) = add_string (dollar^Lib.int_to_string i)
      | pr_term a = add_string(percent^Lib.int_to_string (index a))
in
  begin_block INCONSISTENT 0;
  add_string"`"; pr_term tm; add_string"`"; end_block()
end;



(*---------------------------------------------------------------------------*
 * Hidden information sharing between Term and Net. Term nets need to
 * break terms apart when they are accessed, and it is slow to do this
 * by use of dest_abs.
 *---------------------------------------------------------------------------*)
local fun break_abs(Abs r) = r
        | break_abs _ = raise TERM_ERR"hidden.break_abs" "not an abstraction"
      val used = ref false
in
fun Net_init r =
  if !used then () else (r := break_abs; used := true)
end;


(*---------------------------------------------------------------------------*
 * Hidden information sharing between Term and Preterm.                      *
 *---------------------------------------------------------------------------*)
local val used = ref false
      fun constify{Name,Ty} =
        let val (Const(r,_)) = #const(const_decl Name)
        in Const(r,Ty)
        end
in
fun Preterm_init r1 r2 =
  if !used then () else (r1 := constify; r2 := Comb; used := true)
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
    trv
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
