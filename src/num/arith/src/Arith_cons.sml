(*****************************************************************************)
(* FILE          : arith_cons.sml                                            *)
(* DESCRIPTION   : Constructor, destructor and discriminator functions for   *)
(*                 arithmetic terms.                                         *)
(*                                                                           *)
(* READS FILES   : <none>                                                    *)
(* WRITES FILES  : <none>                                                    *)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 4th March 1991                                            *)
(*                                                                           *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 4th February 1993                                         *)
(*                                                                           *)
(* LAST MODIFIED : R.J.Boulton                                               *)
(* DATE          : 16th November 1995                                        *)
(*****************************************************************************)

structure Arith_cons :> Arith_cons =
struct

open HolKernel Arbint Abbrev;

local open arithmeticTheory in end;

(*===========================================================================*)
(* Constructors, destructors and discriminators for +,-,*                    *)
(*===========================================================================*)

val num_ty = numSyntax.num

(*---------------------------------------------------------------------------*)
(* mk_plus, mk_minus, mk_mult                                                *)
(*---------------------------------------------------------------------------*)

val mk_plus  = numSyntax.mk_plus
and mk_minus = numSyntax.mk_minus
and mk_mult  = numSyntax.mk_mult

(*---------------------------------------------------------------------------*)
(* dest_plus, dest_minus, dest_mult                                          *)
(*---------------------------------------------------------------------------*)

val dest_plus  = numSyntax.dest_plus
and dest_minus = numSyntax.dest_minus
and dest_mult  = numSyntax.dest_mult

(*---------------------------------------------------------------------------*)
(* is_plus, is_minus, is_mult, is_arith_op                                   *)
(*---------------------------------------------------------------------------*)

val is_plus  = numSyntax.is_plus
and is_minus = numSyntax.is_minus
and is_mult  = numSyntax.is_mult

(*===========================================================================*)
(* Constructors, destructors and discriminators for <,<=,>,>=                *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* mk_less, mk_leq, mk_great, mk_geq                                         *)
(*---------------------------------------------------------------------------*)

val mk_less  = numSyntax.mk_less
and mk_leq   = numSyntax.mk_leq
and mk_great = numSyntax.mk_greater
and mk_geq   = numSyntax.mk_geq

(*---------------------------------------------------------------------------*)
(* dest_less, dest_leq, dest_great, dest_geq                                 *)
(*---------------------------------------------------------------------------*)

val dest_less  = numSyntax.dest_less
and dest_leq   = numSyntax.dest_leq
and dest_great = numSyntax.dest_greater
and dest_geq   = numSyntax.dest_geq

(*---------------------------------------------------------------------------*)
(* is_less, is_leq, is_great, is_geq, is_num_reln                            *)
(*---------------------------------------------------------------------------*)

val is_less  = numSyntax.is_less
and is_leq   = numSyntax.is_leq
and is_great = numSyntax.is_greater
and is_geq   = numSyntax.is_geq;

(*===========================================================================*)
(* Constructor, destructor and discriminator for SUC                         *)
(*===========================================================================*)

val mk_suc   = numSyntax.mk_suc
val dest_suc = numSyntax.dest_suc
val is_suc   = numSyntax.is_suc;

(*===========================================================================*)
(* Constructor, destructor and discriminator for PRE                         *)
(*===========================================================================*)

val mk_pre   = numSyntax.mk_pre
val dest_pre = numSyntax.dest_pre
val is_pre   = numSyntax.is_pre

(*===========================================================================*)
(* Discriminators for numbers                                                *)
(*===========================================================================*)

val is_num_const = numSyntax.is_numeral
val zero         = numSyntax.zero_tm
fun is_zero tm   = aconv tm zero


(*===========================================================================*)
(* Conversions between ML integers and numeric constant terms                *)
(*===========================================================================*)

val int_of_term = fromNat o numSyntax.dest_numeral
val term_of_int = numSyntax.mk_numeral o toNat

(*===========================================================================*)
(* Generation of a numeric variable from a name                              *)
(*===========================================================================*)

fun mk_num_var s = mk_var(s,num_ty);

(*===========================================================================*)
(* Functions to extract the arguments from an application of a binary op.    *)
(*===========================================================================*)

val arg1 = rand o rator
and arg2 = rand;

(*===========================================================================*)
(* Is a term a full application of a numerical relation?                     *)
(*===========================================================================*)

local infixr -->
      val num_reln_type = num_ty --> num_ty --> bool
in
fun is_num_reln tm =
  (num_reln_type = type_of(rator(rator tm))) handle HOL_ERR _ => false
end;

end
