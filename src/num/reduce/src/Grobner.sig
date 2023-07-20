(* ========================================================================= *)
(* Generic Grobner Basis algorithm. (HOL-Light's grobner.ml)                 *)
(*                                                                           *)
(* Whatever the instantiation, it basically solves the universal theory of   *)
(* the complex numbers, or equivalently something like the theory of all     *)
(* commutative cancellation semirings with no nilpotent elements and having  *)
(* characteristic zero. We could do "all rings" by a more elaborate integer  *)
(* version of Grobner bases, but I don't have any useful applications.       *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

signature Grobner =
sig
   include Abbrev

   type rat = Arbrat.rat

   (* NOTE: RING_AND_IDEAL_CONV params := (RING params, ideal_cofactors params)

    - structure of "params":

      (ring_dest_const,ring_mk_const,RING_EQ_CONV,
       ring_neg_tm,ring_add_tm,ring_sub_tm,
       ring_inv_tm,ring_mul_tm,ring_div_tm,ring_pow_tm,
       RING_INTEGRAL,RABINOWITSCH_THM,RING_NORMALIZE_CONV)

      where ring_neg_tm (unary), ring_sub_tm (binary), ring_inv_tm (unary) and
      ring_div_tm (binary) are not used if RABINOWITSCH_THM is |- T. In the
      latter case these terms can be created by genvar() from suitable types.

    - statements of RING_INTEGRAL (`add` and `mul` are ring operators):

      |- (!x:'a. mul r0 x = r0) /\
         (!x y z. add x y = add x z <=> y = z) /\
          !w x y z. add (mul w y) (mul x z) = add (mul w z) (mul x y) <=>
                    w = x \/ y = z

    - statements of RABINOWITSCH_THM:

      |- !x y. x <> y <=> ?z. mul (sub x y) z = r1 (or |- T)
    *)
   val RING_AND_IDEAL_CONV : (term -> rat) * (rat -> term) * conv *
                              term * term * term * term * term * term * term *
                              thm * thm * conv ->
                             (term -> thm) * (term list -> term -> term list)

   val RING                : (term -> rat) * (rat -> term) * conv *
                              term * term * term * term * term * term * term *
                              thm * thm * conv ->
                              term -> thm

   val ideal_cofactors     : (term -> rat) * (rat -> term) * conv *
                              term * term * term * term * term * term * term *
                              thm * thm * conv ->
                              term list -> term -> term list

   (* Sample application of RING_AND_IDEAL_CONV to :num *)
   val NUM_SIMPLIFY_CONV   : conv
   val NUM_RING            : term -> thm

   val verbose : bool ref (* default: true *)
end
