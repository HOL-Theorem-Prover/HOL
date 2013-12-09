open arm_progLib;
open arm_saved_specsTheory;

val () = arm_progLib.loadSpecs arm_saved_specsTheory.saved_specs;

use "arm_tests.sml";

val fails = ref ([]:string list);

fun attempt hex =
   arm_spec_hex hex
   handle HOL_ERR _ => (fails := hex::(!fails); [TRUTH]);

val () = (List.map attempt arm_tests; print "Done.\n")

val failed = !fails

val dec = arm_stepLib.arm_decode_hex ""

val l = List.map dec failed
