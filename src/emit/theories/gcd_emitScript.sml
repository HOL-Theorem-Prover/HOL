open HolKernel boolLib bossLib Parse;
open EmitML gcdTheory;
open num_emitTheory;

val _ = new_theory "gcd_emit";

val defs = map DEFN [dividesTheory.compute_divides, GCD_EFFICIENTLY, lcm_def];

val _ = eSML "gcd"
  (MLSIG "type num = numML.num" ::
   OPEN ["num"] ::
   defs);

val _ = eCAML "gcd"
  (MLSIGSTRUCT ["type num = NumML.num"] @
   OPEN ["num"] ::
   defs);

val _ = export_theory ();
