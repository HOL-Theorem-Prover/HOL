(* ===================================================================== *)
(* FILE          : Kind.sml                                              *)
(* DESCRIPTION   : HOL kinds (of types).                                 *)
(*                                                                       *)
(* AUTHOR        : (c) Peter Vincent Homeier                             *)
(* DATE          : May 29, 2009                                          *)
(* ===================================================================== *)

structure Kind :> Kind =
struct

(*
In *scratch*, type
(hol-set-executable sml-executable)
and type Ctrl-j.

loadPath := Globals.HOLDIR ^ "/sigobj" :: !loadPath;
app load ["Feedback","Lib","KernelTypes"];
*)

open Feedback Lib;

infix |-> ##;

val WARN = HOL_WARNING "Kind";
fun ERR f msg = HOL_ERR {origin_structure = "Kind",
                         origin_function = f,
                         message = msg}

datatype kind = Type
              | KdVar of string
              | Oper of kind * kind


(*---------------------------------------------------------------------------
       The kind of HOL types
 ---------------------------------------------------------------------------*)

val typ = Type

(*---------------------------------------------------------------------------
       Operator (arrow) kinds
 ---------------------------------------------------------------------------*)

infixr 3 ==>;   val op ==> = Oper;

fun kind_dom_rng (Oper(X,Y)) = (X,Y)
  | kind_dom_rng _ = raise ERR "kind_dom_rng" "not an operator kind";

fun mk_arity 0 = Type
  | mk_arity n = Type ==> mk_arity (n-1);

fun is_arity (Type) = true
  | is_arity (Oper(Type,Y)) = is_arity Y
  | is_arity _ = false;

fun arity_of (Type) = 0
  | arity_of (Oper(Type,Y)) = arity_of Y + 1
  | arity_of _ = raise ERR "arity_of" "not an arity kind";

fun list_mk_arrow_kind (X::XS,Y) = X ==> list_mk_arrow_kind(XS,Y)
  | list_mk_arrow_kind ( []  ,Y) = Y;

val dest_arrow_kind = kind_dom_rng;

fun strip_arrow_kind (Oper(X,Y)) = let val (args,res) = strip_arrow_kind Y
                                   in (X::args, res)
                                   end
  | strip_arrow_kind Z = ([],Z);


(*---------------------------------------------------------------------------
       Kind variables
 ---------------------------------------------------------------------------*)

val kappa = KdVar "'k"

val varkindcomplain = ref true
val _ = register_btrace ("Varkind Format Complaint", varkindcomplain)

fun mk_var_kind "'k" = kappa
  | mk_var_kind s = if Lexis.allowed_user_type_var s then KdVar s
                    else (if !varkindcomplain then
                            WARN "mk_var_kind" "non-standard syntax"
                          else (); KdVar s)

fun dest_var_kind (KdVar s) = s
  | dest_var_kind _ = raise ERR "dest_var_kind" "not a kind variable"


(*---------------------------------------------------------------------------
     Automatically generated kind variables. The unusual names make
     it unlikely that the names will clash with user-created
     kind variables.
 ---------------------------------------------------------------------------*)
      
local val gen_kdvar_prefix = "%%gen_kdvar%%"
      fun num2name i = gen_kdvar_prefix^Lib.int_to_string i
      val nameStrm   = Lib.mk_istream (fn x => x+1) 0 num2name
in
fun gen_var_kind () = KdVar(state(next nameStrm))

fun is_gen_kdvar (KdVar name) = String.isPrefix gen_kdvar_prefix name
  | is_gen_kdvar _ = false;
end;


(*---------------------------------------------------------------------------
                Discriminators
 ---------------------------------------------------------------------------*)

(* for is_type_kind, use k = typ *)
fun is_base_kind    (Type) = true | is_base_kind  _ = false;
fun is_var_kind (KdVar  _) = true | is_var_kind   _ = false;
fun is_arrow_kind (Oper _) = true | is_arrow_kind _ = false;


(*----------------------------------------------------------------------*
 * The kind variables in a kind.  Tail recursive (from Ken Larsen).     *
 *----------------------------------------------------------------------*)

local fun KV (v as KdVar _) A k   = k (Lib.insert v A)
        | KV (Oper(kd1, kd2)) A k = KV kd1 A (fn q => KV kd2 q k)
        | KV _ A k = k A
      and KVl (kd::kds) A k       = KV kd A (fn q => KVl kds q k)
        | KVl _ A k = k A
in
fun kind_vars kd = rev(KV kd [] Lib.I)
fun kind_varsl L = rev(KVl L [] Lib.I)
end;


(*---------------------------------------------------------------------------
    Does there exist a kind variable v in a kind such that P(v) holds.
    Returns false if there are no kind variables in the kind.
 ---------------------------------------------------------------------------*)
  
fun exists_kdvar P =
 let fun occ (Type) = false
       | occ (w as KdVar _) = P w
       | occ (Oper(kd1,kd2)) = occ kd1 orelse occ kd2
 in occ end;
                         
(*---------------------------------------------------------------------------
     Does a kind variable occur in a kind
 ---------------------------------------------------------------------------*)

fun kind_var_in v = 
  if is_var_kind v then exists_kdvar (equal v)
                   else raise ERR "kind_var_occurs" "not a kind variable"


(*---------------------------------------------------------------------------*
 * Substitute in a kind, trying to preserve existing structure.              *
 *---------------------------------------------------------------------------*)

fun kd_sub [] _ = SAME
  | kd_sub theta (Type) = SAME
  | kd_sub theta (Oper(kd1,kd2))
      = (case delta_map (kd_sub theta) [kd1,kd2]
          of SAME => SAME
           | DIFF [kd1',kd2'] => DIFF (Oper(kd1', kd2'))
           | DIFF _ => raise ERR "kd_sub" "can't happen")
  | kd_sub theta v =
      case Lib.subst_assoc (equal v) theta
       of NONE    => SAME
        | SOME kd => if kd=v then SAME else DIFF kd

fun kd_sub1 theta kd =
  case Lib.subst_assoc (equal kd) theta
   of SOME kd' => if kd'=kd then SAME else DIFF kd'
    | NONE     => (case kd
                    of Oper(kd1,kd2) =>
                         (case delta_map (kd_sub1 theta) [kd1,kd2]
                           of SAME => SAME
                            | DIFF [kd1',kd2'] => DIFF (Oper(kd1',kd2'))
                            | DIFF _ => raise ERR "kd_sub1" "can't happen")
                     | _ => SAME)

fun kind_subst theta =
    if null theta then I
    else if List.all (is_var_kind o #redex) theta
         then delta_apply (kd_sub theta)
         else delta_apply (kd_sub1 theta)

         
(*---------------------------------------------------------------------------
         This matching algorithm keeps track of identity bindings
         v |-> v in a separate area. This eliminates the need for
         post-match normalization of substitutions coming from the
         matching algorithm.
 ---------------------------------------------------------------------------*)
  
local
  fun MERR s = raise ERR "raw_match_kind" s
  fun lookup x ids =
   let fun look [] = if Lib.mem x ids then SOME x else NONE
         | look ({redex,residue}::t) = if x=redex then SOME residue else look t
   in look end
in   
fun kdmatch [] [] Sids = Sids
  | kdmatch (Type::ps) (Type::obs) Sids =
     kdmatch ps obs Sids
  | kdmatch ((v as KdVar name)::ps) (kd::obs) (Sids as (S,ids)) =
     kdmatch ps obs
       (case lookup v ids S
         of NONE => if v=kd then (S,v::ids) else ((v |-> kd)::S,ids)
          | SOME kd1 => if kd1=kd then Sids else
                        MERR ("double bind on kind variable "^name))
  | kdmatch (Oper(p1,p2)::ps) (Oper(obs1,obs2)::obs) Sids =
      kdmatch (p1::p2::ps) (obs1::obs2::obs) Sids
  | kdmatch any other thing = MERR "different kind constructors"
end

fun raw_match_kind pat ob Sids = kdmatch [pat] [ob] Sids 

fun match_kind_restr fixed pat ob  = fst (raw_match_kind pat ob ([],fixed))
fun match_kind_in_context pat ob S = fst (raw_match_kind pat ob (S,[]))

fun match_kind pat ob = match_kind_in_context pat ob []


(* ----------------------------------------------------------------------
    A total ordering on kinds.
    Type < KdVar < Oper
   ---------------------------------------------------------------------- *)

fun kind_compare (Type,     Type)     = EQUAL
  | kind_compare (Type,     _)        = LESS
  | kind_compare (KdVar _,  Type)     = GREATER
  | kind_compare (KdVar s1, KdVar s2) = String.compare(s1,s2)
  | kind_compare (KdVar _,  _)        = LESS
  | kind_compare (Oper p1,  Oper p2)  =
        Lib.pair_compare(kind_compare,kind_compare)(p1,p2)
  | kind_compare (Oper _,   _)        = GREATER;


fun size acc kdlist =
    case kdlist of
      [] => acc
    | [] :: kds => size acc kds
    | (kd::kds1) :: kds2 => let
      in
        case kd of
          Oper(opr, arg) => size acc ((opr :: arg :: kds1) :: kds2)
        | _              => size (1 + acc) (kds1 :: kds2)
      end

fun kind_size kd = size 0 [[kd]]


(*---------------------------------------------------------------------------*
 *  Syntax prettyprinters for kinds.                                         *
 *                                                                           *
 * The following prettyprinter prints kinds which are arities as "ar <n>".   *
 * If possible, the simplest kind (Type) is printed as "*"; kind variables   *
 * are printed as their name (normally beginning with '); else as an arity.  *
 * Otherwise, kinds which are not arities are printed using the infix "->".  *
 * "->" associates to the right, else, parentheses are printed as needed.    *
 *---------------------------------------------------------------------------*)

fun pp_kind pps kn =
 let open Portable
     val {add_string,add_break,begin_block,end_block,...} = with_ppstream pps
     fun pp1 paren (Type) = add_string "ty"
       | pp1 paren (KdVar s) = add_string s
       | pp1 paren (Oper(Rator,Rand)) =
          ( if paren then (add_string "("; begin_block INCONSISTENT 0) else ();
            pp true Rator; add_string " =>"; add_break(1,0); pp false Rand;
            if paren then (end_block(); add_string ")") else () )
     and pp paren Type = add_string "ty"
       | pp paren (KdVar s) = add_string s
       | pp paren kn = add_string ("ar " ^ Lib.int_to_string (arity_of kn))
                       handle HOL_ERR _ => pp1 paren kn
 in
   begin_block INCONSISTENT 0;
   pp false kn;
   end_block()
 end;

fun pp_qkind pps kn =
 let open Portable Globals
     val {add_string,add_break,begin_block,end_block,...} = with_ppstream pps
     val pp_kind = pp_kind pps
 in
   begin_block INCONSISTENT 0;
   add_string (!kind_pp_prefix);
   add_string "::";
   pp_kind kn;
   add_string (!kind_pp_suffix);
   end_block()
 end;

(*---------------------------------------------------------------------------*)
(* Send the results of prettyprinting to a string                            *)
(*---------------------------------------------------------------------------*)

fun sprint pp x = HOLPP.pp_to_string 72 pp x

val kind_to_string = sprint pp_kind;

(*
val _ = installPP pp_qkind;
*)

(*
val k0 = typ;
val k1 = typ ==> typ;
val k2 = mk_arity 2;
val k3 = (typ ==> typ) ==> (typ ==> typ);
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


end (* Kind *)
