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

val ERR = mk_HOL_ERR "fcpSyntax";

(* ------------------------------------------------------------------------- *)
(*   FCP types                                                               *)
(*---------------------------------------------------------------------------*)

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
(*  FCP constants                                                            *)
(* ------------------------------------------------------------------------- *)

fun konst name = Term.prim_mk_const{Name = name, Thy = "fcp"};

val fcp_tm        = konst "FCP"
val fcp_index_tm  = konst "fcp_index"
val dimindex_tm   = konst "dimindex"
val fcp_update_tm = konst  ":+"
val fcp_hd_tm     = konst "FCP_HD"
val fcp_tl_tm     = konst "FCP_TL"
val fcp_cons_tm   = konst "FCP_CONS"
val fcp_map_tm    = konst "FCP_MAP"
val fcp_exists_tm = konst "FCP_EXISTS"
val fcp_every_tm  = konst "FCP_EVERY"
val v2l_tm        = konst "V2L"
val l2v_tm        = konst "L2V";

(* ------------------------------------------------------------------------- *)
(* Constructors                                                              *)
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

(*---------------------------------------------------------------------------*)
(* Note the argument order of mk_fcp_update is different than the order of   *)
(* the arguments to the constant.                                            *)
(*---------------------------------------------------------------------------*)

fun mk_fcp_update (A,i,v) =
 let val (elty,sizety) = dest_cart_type (type_of A)
     val fcp_update_tm' = Term.inst [alpha |-> elty, beta |-> sizety] fcp_update_tm
 in
   list_mk_comb(fcp_update_tm',[i,v,A])
 end
 handle HOL_ERR _ => raise ERR "mk_fcp_update" "";

fun mk_fcp_hd tm =
 let val (elty,sizety) = dest_cart_type (type_of tm)
     val fcp_hd_tm' = Term.inst[alpha |-> elty, beta |-> sizety] fcp_hd_tm
 in mk_comb(fcp_hd_tm',tm)
 end
 handle HOL_ERR _ => raise ERR "mk_fcp_hd" "";

fun mk_fcp_tl tm =
 let val (elty,sizety) = dest_cart_type (type_of tm)
     val fcp_tl_tm' = Term.inst[alpha |-> elty, beta |-> sizety] fcp_tl_tm
 in mk_comb(fcp_tl_tm',tm)
 end
 handle HOL_ERR _ => raise ERR "mk_fcp_tl" "";

fun mk_fcp_cons (h,t) =
 let val (elty,sizety) = dest_cart_type (type_of t)
     val n = dest_numeric_type sizety
     val sizety' = mk_numeric_type (Arbnum.plus1 n)
     val fcp_cons_tm' = Term.inst[alpha |-> elty,
                                  beta |-> sizety, gamma |-> sizety'] fcp_cons_tm
 in list_mk_comb(fcp_cons_tm',[h,t])
 end
 handle HOL_ERR _ => raise ERR "mk_fcp_cons" "";

fun mk_fcp_map (f,A) =
 let val (dom_elty,sizety) = dest_cart_type (type_of A)
     val rng_elty = snd(dom_rng(type_of f))
     val fcp_map_tm' = Term.inst[alpha |-> dom_elty,
                                 beta |-> rng_elty, gamma |-> sizety] fcp_map_tm
 in
   list_mk_comb(fcp_map_tm',[f,A])
 end
 handle HOL_ERR _ => raise ERR "mk_fcp_map" "";

fun mk_fcp_exists (P,A) =
 let val (elty,sizety) = dest_cart_type (type_of A)
     val fcp_exists_tm' = Term.inst[alpha |-> elty,beta |-> sizety] fcp_exists_tm
 in
   list_mk_comb(fcp_exists_tm',[P,A])
 end
 handle HOL_ERR _ => raise ERR "mk_fcp_exists" "";

fun mk_fcp_every (P,A) =
 let val (elty,sizety) = dest_cart_type (type_of A)
     val fcp_every_tm' = Term.inst[alpha |-> elty,beta |-> sizety] fcp_every_tm
 in
   list_mk_comb(fcp_every_tm',[P,A])
 end
 handle HOL_ERR _ => raise ERR "mk_fcp_every" "";

fun mk_v2l A =
 let val (elty,sizety) = dest_cart_type (type_of A)
     val v2l_tm' = Term.inst[alpha |-> elty,beta |-> sizety] v2l_tm
 in
   mk_comb(v2l_tm',A)
 end
 handle HOL_ERR _ => raise ERR "mk_v2l" "";

fun mk_l2v Ltm =
 let val (els,elty) = listSyntax.dest_list Ltm
     val n = Arbnum.fromInt (length els)
     val nty = mk_numeric_type n
     val l2v_tm' = Term.inst[alpha |-> elty,beta |-> nty] l2v_tm
 in
   mk_comb(l2v_tm',Ltm)
 end
 handle HOL_ERR _ => raise ERR "mk_l2v" "";

(* ------------------------------------------------------------------------- *)
(*  Destructors                                                              *)
(* ------------------------------------------------------------------------- *)

fun dest_fcp tm =
  (HolKernel.dest_monop fcp_tm (ERR "dest_fcp" "") tm,
   snd (dest_cart_type (type_of tm)));

val dest_fcp_index =
  HolKernel.dest_binop fcp_index_tm (ERR "dest_fcp_index" "");

fun dest_dimindex tm =
  HolKernel.dest_monop dimindex_tm (ERR "dest_dimindex" "") tm
    |> boolSyntax.dest_itself;

fun dest_fcp_update tm =
  let val (i,v,A) = HolKernel.dest_triop fcp_update_tm
                                    (ERR "dest_fcp_update" "") tm
  in (A,i,v)
  end

val dest_fcp_hd =
  HolKernel.dest_monop fcp_hd_tm (ERR "dest_fcp_hd" "");

val dest_fcp_tl =
  HolKernel.dest_monop fcp_tl_tm (ERR "dest_fcp_tl" "");

val dest_fcp_cons =
  HolKernel.dest_binop fcp_cons_tm (ERR "dest_fcp_cons" "");

val dest_fcp_map =
  HolKernel.dest_binop fcp_map_tm (ERR "dest_fcp_map" "");

val dest_fcp_exists =
  HolKernel.dest_binop fcp_exists_tm (ERR "dest_fcp_exists" "");

val dest_fcp_every =
  HolKernel.dest_binop fcp_every_tm (ERR "dest_fcp_every" "");

val dest_v2l =
  HolKernel.dest_monop v2l_tm (ERR "dest_v2l" "");

val dest_l2v =
  HolKernel.dest_monop l2v_tm (ERR "dest_l2v" "");


(* ------------------------------------------------------------------------- *)
(*  Discriminators                                                           *)
(* ------------------------------------------------------------------------- *)

val is_fcp       = Lib.can dest_fcp;
val is_fcp_index = Lib.can dest_fcp_index;
val is_dimindex  = Lib.can dest_dimindex;

val is_fcp_update = can dest_fcp_update;
val is_fcp_hd     = can dest_fcp_hd
val is_fcp_tl     = can dest_fcp_tl
val is_fcp_cons   = can dest_fcp_cons
val is_fcp_map    = can dest_fcp_map
val is_fcp_exists = can dest_fcp_exists
val is_fcp_every  = can dest_fcp_every
val is_v2l        = can dest_v2l
val is_l2v        = can dest_l2v;

(* ------------------------------------------------------------------------- *)

end
