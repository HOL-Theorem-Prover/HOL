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

datatype hol_type = Utv of string              (* User-given type variables *)
                  | Tyapp of tyc * hol_type list;


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
  | mk_vartype s = if Lexis.allowed_user_type_var s then Utv s
      else raise TYPE_ERR "mk_vartype" "incorrect syntax"
end;

val alpha = mk_vartype "'a"
val beta  = mk_vartype "'b";


(*---------------------------------------------------------------------------*
 * It makes sense to declare the type construction primitives in the place   *
 * where the type signature is declared and manipulated, ie. it makes sense  *
 * to declare and manipulate the type sig. in the structure Theory. However, *
 * Theory is defined after theorems have been defined. It is also necessary  *
 * to have type construction be a part of Type. Hence, I need a "backward"   *
 * reference from Theory to Type.                                            *
 *---------------------------------------------------------------------------*)
local val mk_type_ref  = ref (fn _:{Tyop:string,Args:hol_type list} => alpha)
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
 * A total ordering on types. Utv < Tyapp                                    *
 *---------------------------------------------------------------------------*)
fun type_lt (Utv s1) (Utv s2) = (s1<s2)
  | type_lt (Utv _) _ = true

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

fun type_subst theta ty =
    case (ty_sub theta ty)
      of SAME     => ty
       | DIFF ty' => ty';


(*---------------------------------------------------------------------------*
 * Is a type polymorphic?                                                    *
 *---------------------------------------------------------------------------*)
fun polymorphic (Utv _) = true
  | polymorphic (Tyapp(_,Args)) = exists polymorphic Args


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
