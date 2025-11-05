Theory gh225a[bare]
Libs
  HolKernel Parse boolLib

(* Cannot use Theorem syntax here, as Empty and GREATER would be interpreted
 * as patterns instead of identifiers. *)
val _ = save_thm("Empty", TRUTH);
val _ = save_thm("GREATER", TRUTH);
