(* ===================================================================== *)
(* FILE          : Kind.sml                                              *)
(* DESCRIPTION   : HOL kinds (of types).                                 *)
(*                                                                       *)
(* AUTHOR        : (c) Peter Vincent Homeier                             *)
(* DATE          : September 10, 2007                                    *)
(* ===================================================================== *)

structure Kind : RawKind =
struct

(*
In *scratch*, type
(hol-set-executable mosml-executable)
and type Ctrl-j.

loadPath := "/usr/local/hol/hol98/kananaskis-5-2p/hol98/sigobj" :: !loadPath;
app load ["Feedback","Lib","KernelTypes"];
*)

open Feedback Lib KernelTypes;   infix |-> ##;

type kind = KernelTypes.kind;

val ERR = mk_HOL_ERR "Kind";
val WARN = HOL_WARNING "Kind";


(*---------------------------------------------------------------------------
       The kind of HOL types
 ---------------------------------------------------------------------------*)

val typ = Type

(*---------------------------------------------------------------------------
       Operator kinds
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


(* ----------------------------------------------------------------------
    A total ordering on kinds.
    Type < Oper
   ---------------------------------------------------------------------- *)

fun kind_compare (Type, Type)   = EQUAL
  | kind_compare (Type, _)      = LESS
  | kind_compare (Oper _, Type) = GREATER
  | kind_compare (Oper p1, Oper p2) =
        Lib.pair_compare(kind_compare,kind_compare)(p1,p2);


(*---------------------------------------------------------------------------*
 *  Syntax prettyprinters for kinds.                                         *
 *                                                                           *
 * The following prettyprinter prints kinds which are arities as "ar <n>".   *
 * If possible, the simplest kind (Type) is printed as "*"; else as an arity.*
 * Otherwise, kinds which are not arities are printed using the infix "->".  *
 * "->" associates to the right, else, parentheses are printed as needed.    *
 *---------------------------------------------------------------------------*)

fun pp_kind pps kn =
 let open Portable
     val {add_string,add_break,begin_block,end_block,...} = with_ppstream pps
     fun pp1 paren (Type) = add_string "ty"
       | pp1 paren (Oper(Rator,Rand)) =
          ( if paren then (add_string "("; begin_block INCONSISTENT 0) else ();
            pp true Rator; add_string " =>"; add_break(1,0); pp false Rand;
            if paren then (end_block(); add_string ")") else () )
     and pp paren Type = add_string "ty"
       | pp paren kn = add_string ("ar " ^ Lib.int_to_string (arity_of kn))
                       handle HOL_ERR _ => pp1 paren kn
 in
   begin_block INCONSISTENT 0;
   pp false kn;
   end_block()
 end;

fun pp_qkind pps kn =
 let open Portable
     val {add_string,add_break,begin_block,end_block,...} = with_ppstream pps
     val pp_kind = pp_kind pps
 in
   begin_block INCONSISTENT 0;
   add_string "``::";
   pp_kind kn;
   add_string "``";
   end_block()
 end;

(*---------------------------------------------------------------------------*)
(* Send the results of prettyprinting to a string                            *)
(*---------------------------------------------------------------------------*)

fun sprint pp x = PP.pp_to_string 72 pp x

val kind_to_string = sprint pp_kind;

(*
val _ = installPP pp_kind;
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
