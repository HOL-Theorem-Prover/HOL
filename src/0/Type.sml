(* ===================================================================== *)
(* FILE          : type.sml                                              *)
(* DESCRIPTION   : HOL types.                                            *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : August 26, 1991                                       *)
(* UPDATE        : October 94. Type signature implementation moved from  *)
(*                 symtab.sml, which is now gone.                        *)
(* Modified      : September 22, 1997, Ken Larsen                        *)
(*                 April 12, 1998, Konrad Slind                          *)
(* ===================================================================== *)

structure Type :> Type =
struct

open Exception Lib;

fun TYPE_ERR function message = 
     HOL_ERR{origin_structure = "Type",
             origin_function = function,
             message = message}


type tyc = {name:string, revision:int};

datatype hol_type = Stv of int           (* System generated type variables *)
                  | Utv of string              (* User-given type variables *)
                  | Link of hol_type ref             (* Modifiable pointers *)
                  | Tyapp of tyc * hol_type list;


(*---------------------------------------------------------------------------*
 * A dummy type. Not constructible by users.                                 *
 *---------------------------------------------------------------------------*)
val dummy = Utv"dummy";


(*---------------------------------------------------------------------------*
 * It makes sense to declare the type construction primitives in the place   *
 * where the type signature is declared and manipulated, ie. it makes sense  *
 * to declare and manipulate the type sig. in the structure Theory. However, *
 * Theory is defined after theorems have been defined. It is also necessary  *
 * to have type construction be a part of Type. Hence, I need a "backward"   *
 * reference from Theory to Type.                                            *
 *---------------------------------------------------------------------------*)
local val mk_type_ref  = ref (fn _:{Tyop:string,Args:hol_type list} => dummy)
      val current_revision_ref  = ref (fn _:string => ~1)
      val started = ref false
in
  fun init f g = 
   if !started then ()
   else (mk_type_ref := f; current_revision_ref := g; started := true)

  fun mk_type x = !mk_type_ref x
  fun current_revision s = !current_revision_ref s
end;

(*---------------------------------------------------------------------------*
 * Builtins. These are in every HOL signature, and it is convenient to nail  *
 * them down here, so that, e.g., some functions in Dsyntax are relatively   *
 * efficient.                                                                *
 *---------------------------------------------------------------------------*)
infixr 3 -->
fun (X --> Y) = Tyapp({name ="fun", revision=0}, [X,Y]);
val bool = Tyapp({name="bool",revision=0},[]);


(*---------------------------------------------------------------------------*
 * Take a type apart.                                                        *
 *---------------------------------------------------------------------------*)
fun dest_type (Tyapp({name,...},args)) = {Tyop=name,Args=args}
  | dest_type _ = raise TYPE_ERR "dest_type" "";


(*---------------------------------------------------------------------------*
 * Invert -->.                                                               *
 *---------------------------------------------------------------------------*)
fun dom_rng ty = 
    case dest_type ty
     of {Tyop="fun", Args=[x,y]} => (x,y)
      | _ => raise TYPE_ERR "dom_rng" "not a function type";


(*---------------------------------------------------------------------------*
 * Make a type variable. Simple sharing scheme. A bonafide hash table        *
 * would be better.                                                          *
 *---------------------------------------------------------------------------*)
local val a = Utv "'a"      val b  = Utv "'b"   
      val c = Utv "'c"      val d  = Utv "'d"
      val e = Utv "'e"      val f  = Utv "'f"   
in
fun mk_vartype "'a" = a  | mk_vartype "'b" = b
  | mk_vartype "'c" = c  | mk_vartype "'d" = d
  | mk_vartype "'e" = e  | mk_vartype "'f" = f
  | mk_vartype s = if (Lexis.allowed_user_type_var s) then Utv s
      else raise TYPE_ERR "mk_vartype" "incorrect syntax"
end;

val alpha = mk_vartype "'a"
val beta = mk_vartype "'b";

(*---------------------------------------------------------------------------*
 * Take a type variable apart.                                               *
 *---------------------------------------------------------------------------*)
fun dest_vartype (Utv s) = s
  | dest_vartype _ = raise TYPE_ERR "dest_vartype" "not a type variable";

val is_vartype = can dest_vartype;


(*---------------------------------------------------------------------------*
 * The variables in a type.                                                  *
 *---------------------------------------------------------------------------*)
local
fun tyvars (v as Utv _) vlist = if (mem v vlist) then vlist else v::vlist
  | tyvars (Tyapp(_,Args)) vlist = tyvarsl Args vlist
  | tyvars _ _ = raise TYPE_ERR "tyvars" "type construction"
and
    tyvarsl L vlist = rev_itlist tyvars L vlist
in
fun type_vars ty = rev(tyvars ty [])
fun type_varsl L = rev(tyvarsl L [])
end;


(*---------------------------------------------------------------------------*
 * Extends an ordering on elements of a type to an ordering on lists of      *
 * elements of that type.                                                    *
 *---------------------------------------------------------------------------*)
fun lex_order order =
   let fun ordered (t1::rst1) (t2::rst2) =
           if (order t1 t2) then true else 
           if (order t2 t1) then false
           else ordered rst1 rst2
         | ordered [] [] = false
         | ordered [] _  = true
         | ordered _  _  = false
   in ordered 
   end;

(*---------------------------------------------------------------------------*
 * A total ordering on types. Stv < Utv < Link < Tyapp                       *
 *---------------------------------------------------------------------------*)
fun type_lt (Stv i1) (Stv i2) = (i1<i2)
  | type_lt (Stv _) _ = true

  | type_lt (Utv _) (Stv _)  = false
  | type_lt (Utv s1) (Utv s2) = (s1<s2)
  | type_lt (Utv _) _ = true

  | type_lt (Link (ref ty1)) (Link (ref ty2)) = type_lt ty1 ty2
  | type_lt (Link _) (Tyapp _) = true
  | type_lt (Link _) _ = false

  | type_lt (Tyapp({name=s1,...},L1)) (Tyapp({name=s2,...},L2)) =
       (case String.compare(s1,s2)
         of LESS => true
          | EQUAL => lex_order type_lt L1 L2
          | GREATER => false)
  | type_lt (Tyapp _) _ = false;


fun type_compare ty1 ty2 = 
    if (ty1=ty2) then EQUAL
    else if type_lt ty1 ty2 then LESS else GREATER;

(*---------------------------------------------------------------------------*
 * System type variable streams. Used in type inference.                     *
 *---------------------------------------------------------------------------*)
local fun step i = Link(ref(Stv(i+1)))
in
 fun fresh_tyvar_stream() = Lib.mk_istream (fn x => x+1) 0 step
end;


(*---------------------------------------------------------------------------*
 * An "all" function defined for uncurried predicates.                       *
 *---------------------------------------------------------------------------*)
fun pr_all2 f =
   let fun trav (a1::rst1) (a2::rst2) = f(a1,a2) andalso trav rst1 rst2
         | trav [] [] = true
         | trav _ _ = false
   in trav
   end;


(*---------------------------------------------------------------------------*
 * Are two types equal? This is Standard ML. A non-Standard version could    *
 * replace the "=" test with something like what is done in Term.aconv:      *
 *                                                                           *
 *    open System.Unsafe  (NJSML only)                                       *
 *    fun EQ (M:hol_type,N:hol_type) = ((cast M:int) = (cast N:int))         *
 *                                                                           *
 *---------------------------------------------------------------------------*)
fun ty_eq pr = 
   (op =) pr orelse 
   (case pr
      of (Tyapp(tyrec1,A1),Tyapp(tyrec2,A2)) =>
                 ((tyrec1=tyrec2) andalso pr_all2 ty_eq A1 A2)
       | (Link(ref ty1), Link(ref ty2)) => ty_eq(ty1,ty2)
       | (Link(ref ty1),ty2)  => ty_eq(ty1,ty2)
       | (ty1, Link(ref ty2)) => ty_eq(ty1,ty2)
       | _ => false);

(*---------------------------------------------------------------------------*
 * The occurs check. We know that the first argument is an Stv.              *
 *---------------------------------------------------------------------------*)
fun occurs v =
   let fun occ (Tyapp(_,Args)) = exists occ Args
         | occ (Link (ref ty)) = occ ty
         | occ ty = (v = ty)
   in occ
   end;

(*---------------------------------------------------------------------------*
 * Various error messages for unification                                    *
 *---------------------------------------------------------------------------*)
val UNIFY_ERR = TYPE_ERR "unify";
val INEQUAL_CONST_ERR = UNIFY_ERR "inequal constants";
val OCCUR_CHECK = UNIFY_ERR "occurs check";


(*---------------------------------------------------------------------------*
 * Unification of types by pointer redirection.                              *
 *                                                                           *
 * The order of the first three clauses of unif is delicate. They ensure     *
 * that the hol_type in the first argument, if it is an assignable variable, *
 * gets assigned.                                                            *
 *---------------------------------------------------------------------------*)
fun unify ty1 ty2 = if ty_eq(ty1,ty2) then () else unif(ty1,ty2)
and unif (Link(r as ref(s as Stv _)), ty) = 
        if (occurs s ty) then raise OCCUR_CHECK else r := ty
  | unif (Link(ref ty1), ty2)          = unify ty1 ty2
  | unif (ty, v as Link (ref (Stv _))) = unify v ty
  | unif (ty1, Link (ref ty2))         = unify ty1 ty2
  | unif (Tyapp(tyrec1,args1), Tyapp(tyrec2, args2)) =
        if (tyrec1 <> tyrec2) then raise INEQUAL_CONST_ERR
        else rev_itlist2 (fn ty1 => K o unify ty1) args1 args2 ()
  | unif _ = raise UNIFY_ERR "structural difference in types";



fun shrink_type alist =
  let fun shrink (Link(ref ty)) = shrink ty
        | shrink (Tyapp(r,Args)) = Tyapp(r, map shrink Args)
        | shrink (s as Stv _) = assoc s alist
        | shrink ty = ty
  in shrink
  end;


fun tyvars (v as Utv _) vlist = insert v vlist
  | tyvars (v as Stv _) vlist = insert v vlist
  | tyvars (Tyapp(_,[])) vlist = vlist
  | tyvars (Tyapp(_,Args)) vlist = rev_itlist tyvars Args vlist
  | tyvars (Link(ref ty)) vlist = tyvars ty vlist;

(*---------------------------------------------------------------------------*
 * Support datatypes and functions.                                          *
 *---------------------------------------------------------------------------*)
datatype 'a delta = SAME | DIFF of 'a;
datatype 'a args_changed = YUP of 'a list | NOPE of 'a list;

fun apply f ty = 
 let val v = f ty
     fun appl(YUP L) = YUP((case v of SAME => ty | DIFF x => x)::L)
       | appl(NOPE L) = case v 
                        of SAME     => NOPE(ty::L)
                         | DIFF ty' => YUP(ty'::L)
   in appl end   ;


(*---------------------------------------------------------------------------*
 * Maps from hol_type to hol_type, with type variables consistently renamed. *
 *---------------------------------------------------------------------------*)

local val tv_pair_list = ref ([]:(hol_type * hol_type) list)
in
fun rename_tv tyvars = 
  let val _ = tv_pair_list := []
      fun rn (v as Utv _) = DIFF
                (assoc v (!tv_pair_list) handle HOL_ERR _
                 => let val v' = Lib.state(Lib.next tyvars)
                    in tv_pair_list := ((v,v')::(!tv_pair_list));  v'   end)
        | rn (Tyapp(tyrec, Args)) = 
           (case (itlist (apply rn) Args (NOPE[]))
            of YUP l  => DIFF(Tyapp(tyrec,l))
             | NOPE _ => SAME)
        | rn _ = raise TYPE_ERR "rename_tv" "type construction"
  in rn
end end;


(*---------------------------------------------------------------------------*
 * Substitute in a type.                                                     *
 *---------------------------------------------------------------------------*)

fun ty_sub []  ty    = SAME
  | ty_sub theta (v as Utv _) = 
      (case (Lib.subst_assoc (fn x => (x = v)) theta)
         of NONE    => SAME
          | SOME ty => DIFF ty)
  | ty_sub theta (Tyapp(tyrec,Args)) =
      (case (itlist (apply (ty_sub theta)) Args (NOPE[]))
         of YUP l' => DIFF (Tyapp(tyrec,l'))
          | NOPE _ => SAME)
  | ty_sub _ _ = raise TYPE_ERR "ty_sub" "type construction";
                                                
fun type_subst theta ty = 
    case (ty_sub theta ty)
      of SAME     => ty
       | DIFF ty' => ty';


(*---------------------------------------------------------------------------*
 * Is a type polymorphic?                                                    *
 *---------------------------------------------------------------------------*)
fun polymorphic (Utv _) = true
  | polymorphic (Tyapp(_,Args)) = exists polymorphic Args
  | polymorphic _ = raise TYPE_ERR"polymorphic" "type construction";


(*---------------------------------------------------------------------------*
 * Matching for types.                                                       *
 *---------------------------------------------------------------------------*)

fun lookup i = Lib.subst_assoc (fn x => x = i);
val MTY_ERR = TYPE_ERR "type_reduce" "";
infix |->;

fun type_reduce (v as Utv _) ty S = 
     (case (lookup v S)
       of NONE => (v |-> ty)::S
        | SOME residue => if (residue=ty) then S else raise MTY_ERR)
  | type_reduce (pat as Tyapp(frec1, args1))
                (ob as  Tyapp(frec2, args2)) S = 
      if (frec1=frec2) then Lib.rev_itlist2 type_reduce args1 args2 S
      else raise MTY_ERR
  | type_reduce _  _  _ = raise MTY_ERR;


local fun del [] A = A
        | del ((rr as {redex,residue})::rst) A =
           if (redex=residue) then del rst A else del rst (rr::A)
in
  fun match_type pat ob = del (type_reduce pat ob []) []
end;


(*---------------------------------------------------------------------------*
 *                                                                           *
 *                         Type Pretty Printer                               *
 *                                                                           *
 *---------------------------------------------------------------------------*)

open Portable_PrettyPrint;
type gravity = gravity
val space = " ";

fun ty_prec "fun" = INFIX 0
  | ty_prec "sum" = INFIX 1
  | ty_prec "prod"  = INFIX 2
  | ty_prec _ = raise TYPE_ERR "ty_prec" "bogus infix";

fun is_infix_tyop "fun" = true
  | is_infix_tyop "sum" = true
  | is_infix_tyop "prod" = true
  | is_infix_tyop _ = false;

fun infix_to_string "fun" = "->"
  | infix_to_string "sum" = "+"
  | infix_to_string "prod" = "#"
  | infix_to_string _ = raise TYPE_ERR "infix_to_string" "bogus infix";

fun strip_infix_ty str (ty as Tyapp({name,...}, [ty1,ty2])) L =
      if (str = name) then strip_infix_ty str ty2 (ty1::L) else rev(ty::L)
  | strip_infix_ty str ty L = rev (ty::L);


(* Returns a list of strings and a type *)
fun strip_singleton_ty (Tyapp(nr, [ty])) L =
         strip_singleton_ty ty (nr::L)
  | strip_singleton_ty ty L = (ty,L)


fun cname {name,revision} =
  if ((revision = current_revision name) handle HOL_ERR _ => false)
  then name else !Globals.old name;

local
val pr_type_ref : (ppstream -> hol_type -> gravity -> int -> unit) ref =
   ref (fn _ => fn _ => fn _ => fn _ => ())

fun initial_pr_type ppstrm =
 let val {add_string,add_break,begin_block,end_block,...} = 
            with_ppstream ppstrm
     val add_lparen = add_lparen ppstrm
     val add_rparen = add_rparen ppstrm
     fun pr_ty_hook ty grav n = (!pr_type_ref) ppstrm ty grav n
     fun pr_ty _ _ 0 = add_string "..."
       | pr_ty(Utv x) _ _ = add_string x
       | pr_ty(Stv i) _ _ = add_string("?"^Lib.int_to_string i)
       | pr_ty(Link(ref ty)) grav n = pr_ty_hook ty grav n
       | pr_ty(Tyapp(nr,[])) _ _ = add_string (cname nr)
       | pr_ty(ty as Tyapp(nr as {name,revision},Args)) grav n = 
           ( begin_block INCONSISTENT 0;
             if (is_infix_tyop name)  
             then let val prec = ty_prec name
                      val name' = cname nr
                  in
                    add_lparen grav prec;
                    Portable_PrettyPrint.pr_list
                       (fn ty => pr_ty_hook ty prec (n-1))
                       (fn () => 
                         if (!(#infix_at_front(Globals.pp_flags)))
                         then add_break(1,0)
                         else add_string (space^infix_to_string name'))
                       (fn () => 
                         if (!(#infix_at_front(Globals.pp_flags)))
                         then add_string (infix_to_string name' ^space)
                         else add_break(1,0))
                       (strip_infix_ty name ty []);
                      add_rparen grav prec
                  end
             else if (length Args = 1)
                  then let val (ty,L) = strip_singleton_ty ty []
                       in
                         add_lparen grav APPL;
                         pr_ty_hook ty APPL (n-1);
                         add_break(1,0);
                         Portable_PrettyPrint.pr_list
                            (fn nr => add_string (cname nr))
                            (fn () => ())
                            (fn () => add_break(1,0))  L;
                         add_rparen grav APPL
                       end
                  else ( add_lparen grav APPL;
                         add_string "(";
                         Portable_PrettyPrint.pr_list 
                            (fn ty => pr_ty_hook ty BOTTOM (n-1)) 
                            (fn () => add_string ",")
                            (fn () => add_break(0,0))  Args;
                         add_string ")";
                         add_string (cname nr);
                         add_rparen grav APPL
                       )
             ;
             end_block()
           )
 in 
    pr_ty
 end;
       
val _ = pr_type_ref := initial_pr_type;

in

fun pr_type ppstrm ty grav n = (!pr_type_ref) ppstrm ty grav n;

fun extend_pp_type print_fun =
   let val old_pr_type = !pr_type_ref
       fun new_pr_type ppstrm ty grav n =
          let fun pr_type {depth,gravity} ty ppstrm =
                 (!pr_type_ref) ppstrm ty gravity depth
          in  (print_fun pr_type {depth=n,gravity=grav} ty ppstrm)
              handle HOL_ERR _ => (old_pr_type ppstrm ty grav n)
          end
   in  pr_type_ref := new_pr_type
   end;

fun reset_pp_type () = (pr_type_ref := initial_pr_type);

end;


fun pp_type ppstrm ty n = pr_type ppstrm ty BOTTOM n


(*---------------------------------------------------------------------------*
 * Information hiding with Parse_support.                                    *
 *---------------------------------------------------------------------------*)
local val used = ref false
in
 fun Ps_init r = 
  if !used then () else (r := rename_tv ; used := true)
end;


(*---------------------------------------------------------------------------*
 * Information hiding with Preterm.                                          *
 *---------------------------------------------------------------------------*)
local val used = ref false
      fun chase (Tyapp({name="fun",...}, [_,ty])) = ty
        | chase (Link(ref ty)) = chase ty
        | chase _ = raise TYPE_ERR"chase" ""
in
 fun Preterm_init r1 r2 r3 r4 = 
  if !used then () 
  else (r1 := unify; r2 := shrink_type; 
        r3 := chase; r4 := tyvars;
        used := true)
end;


(*---------------------------------------------------------------------------*
 * Information hiding with Theory.                                           *
 *---------------------------------------------------------------------------*)
local val used = ref false
      fun break_type (Tyapp x) = x
        | break_type _ = raise TYPE_ERR"break_type" ""
in
 fun Theory_init r1 r2 = 
     if !used then () 
      else (r1 := Tyapp; r2 := break_type; used := true)
end;

end; (* Type *)
