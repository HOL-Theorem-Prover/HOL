structure integerRingLib :> integerRingLib =
struct

(*
load "integerRingTheory";
load "ringLib";
*)

open HolKernel Parse boolLib integerTheory integerRingTheory
     
infix THEN THENL THENC o;
infix 8 by;


val num_to_int = intSyntax.int_injection;
val int_0 = intSyntax.zero_tm
val int_1 = intSyntax.one_tm
fun is_closed_int t =
  mem t [int_0,int_1] orelse
    ((is_comb t) andalso (rator t)=num_to_int) andalso 
     (numSyntax.is_numeral (rand t));

val _ = ringLib.declare_ring
    { RingThm = int_ring_thms,
      IsConst = is_closed_int,
      Rewrites = [int_rewrites, numRingTheory.num_rewrites] };

(* dealing with subtraction: *)
val PRE_CONV = REWRITE_CONV[int_sub]

val POST_CONV =
  REWRITE_CONV[GSYM INT_NEG_MINUS1] THENC
  REWRITE_CONV[GSYM INT_NEG_LMUL, GSYM int_sub]
;

val INT_RING_CONV = PRE_CONV THENC ringLib.RING_CONV THENC POST_CONV;
val INT_NORM_CONV = PRE_CONV THENC ringLib.RING_NORM_CONV THENC POST_CONV;

val INT_RING_TAC = CONV_TAC INT_RING_CONV
val INT_NORM_TAC = CONV_TAC INT_NORM_CONV

val INT_RING_RULE = CONV_RULE INT_RING_CONV
val INT_NORM_RULE = CONV_RULE INT_NORM_CONV

end;
