structure numRingLib :> numRingLib =
struct

open HolKernel Parse numRingTheory;

val _ = ringLib.declare_ring
    { RingThm = num_ring_thms,
      IsConst = numSyntax.is_numeral,
      Rewrites = [num_rewrites] };

val NUM_RING_CONV = ringLib.RING_CONV;
val NUM_NORM_CONV = ringLib.RING_NORM_CONV;

end;
