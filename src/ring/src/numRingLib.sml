structure numRingLib :> numRingLib =
struct

open boolLib numRingTheory; infix THENC;

val _ = ringLib.declare_ring
    { RingThm = num_ring_thms,
      IsConst = numSyntax.is_numeral,
      Rewrites = [num_rewrites] };

val NUM_RING_CONV = REWRITE_CONV [arithmeticTheory.ADD1]
                        THENC ringLib.RING_CONV;

val NUM_NORM_CONV = REWRITE_CONV [arithmeticTheory.ADD1]
                      THENC ringLib.RING_NORM_CONV;

val NUM_RING_TAC = CONV_TAC NUM_RING_CONV
val NUM_NORM_TAC = CONV_TAC NUM_NORM_CONV;

val NUM_RING_RULE = CONV_RULE NUM_RING_CONV
val NUM_NORM_RULE = CONV_RULE NUM_NORM_CONV;

end;
