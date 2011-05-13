(* ========================================================================= *)
(* FILE          : fcpSyntax.sml                                             *)
(* DESCRIPTION   : Syntax support for fcpTheory.                             *)
(* ========================================================================= *)

structure fcpSyntax :> fcpSyntax =
struct

(* interactive use:
  app load ["fcpTheory"];
*)

open HolKernel Parse boolLib bossLib;
open fcpTheory;

val ERR = mk_HOL_ERR "wordsSyntax";

(* ------------------------------------------------------------------------- *)

fun mk_numeric_type n =
  let open Arbnum in
    if mod2 n = zero then
      if n = zero then
        raise ERR "mk_numeric_type" "must be non-zero"
      else
        Type.mk_type("bit0", [mk_numeric_type (div2 n)])
    else
      if n = one then
        Type.mk_type("one", [])
      else
        Type.mk_type("bit1", [mk_numeric_type (div2 (less1 n))])
  end;

val mk_int_numeric_type = mk_numeric_type o Arbnum.fromInt;

fun dest_numeric_type typ =
  case Type.dest_type typ of
    ("one", []) => Arbnum.one
  | ("bit0", [t]) => Arbnum.times2 (dest_numeric_type t)
  | ("bit1", [t]) => Arbnum.plus1 (Arbnum.times2 (dest_numeric_type t))
  | ("sum",  [t,p]) => Arbnum.+(dest_numeric_type t, dest_numeric_type p)
  | ("prod", [t,p]) => Arbnum.*(dest_numeric_type t, dest_numeric_type p)
  | ("fun",  [t,p]) => Arbnum.pow(dest_numeric_type p, dest_numeric_type t)
  | ("cart", [t,p]) => Arbnum.pow(dest_numeric_type t, dest_numeric_type p)
  | _ => raise ERR "dest_numeric_type"
           ("Cannot compute size of type: " ^ Hol_pp.type_to_string typ);

val dest_int_numeric_type = Arbnum.toInt o dest_numeric_type;

val is_numeric_type = Lib.can dest_numeric_type;

fun mk_cart_type (a, b) =
  Type.mk_thy_type {Tyop = "cart", Thy = "fcp", Args = [a,b]};

fun dest_cart_type ty =
  case Lib.total Type.dest_thy_type ty
  of SOME {Tyop = "cart", Thy = "fcp", Args = [a,b]} => (a,b)
   | _ => raise ERR "dest_cart_types" "";

val is_cart_type = Lib.can dest_cart_type;

val dim_of = snd o dest_cart_type o Term.type_of;

(* ------------------------------------------------------------------------- *)

val fcp_tm       = Term.prim_mk_const{Name = "FCP", Thy = "fcp"}
val fcp_index_tm = Term.prim_mk_const{Name = "fcp_index", Thy = "fcp"}
val dimindex_tm  = Term.prim_mk_const{Name = "dimindex", Thy = "fcp"}

(* ------------------------------------------------------------------------- *)

fun mk_fcp (x,ty) =
let val a = snd (Type.dom_rng (Term.type_of x)) in
  Term.mk_comb
    (Term.inst[Type.alpha |-> a, Type.beta |-> ty] fcp_tm, x)
end handle HOL_ERR _ => raise ERR "mk_fcp" "";

fun mk_fcp_index (x,y) =
let val (a, b) = dest_cart_type (Term.type_of x) in
  Term.list_mk_comb
    (Term.inst[Type.alpha |-> a, Type.beta |-> b] fcp_index_tm, [x, y])
end handle HOL_ERR _ => raise ERR "mk_fcp_index" "";

fun mk_dimindex ty =
  Term.mk_comb (Term.inst [Type.alpha |-> ty] dimindex_tm,
                boolSyntax.mk_itself ty)
  handle HOL_ERR _ => raise ERR "mk_dimindex" "";

(* ------------------------------------------------------------------------- *)

fun dest_fcp tm =
  (HolKernel.dest_monop fcp_tm (ERR "dest_fcp" "") tm,
   snd (dest_cart_type (type_of tm)));

val dest_fcp_index =
  HolKernel.dest_binop fcp_index_tm (ERR "dest_fcp_index" "");

fun dest_dimindex tm =
  HolKernel.dest_monop dimindex_tm (ERR "dest_dimword" "") tm
    |> boolSyntax.dest_itself;

(* ------------------------------------------------------------------------- *)

val is_fcp       = Lib.can dest_fcp;
val is_fcp_index = Lib.can dest_fcp_index;
val is_dimindex  = Lib.can dest_dimindex;

(* ------------------------------------------------------------------------- *)

end
