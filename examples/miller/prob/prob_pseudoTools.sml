(* ------------------------------------------------------------------------- *)
(* Coversions for evaluating the pseudo-random number generator.             *)
(* ------------------------------------------------------------------------- *)

structure prob_pseudoTools :> prob_pseudoTools =
struct

open HolKernel Parse boolLib reduceLib prob_pseudoTheory;

infix THENC;

val PROB_PSEUDO_SHD_CONV = REWR_CONV SHD_PROB_PSEUDO THENC REDUCE_CONV;

val PROB_PSEUDO_STL_CONV =
  REWR_CONV STL_PROB_PSEUDO THENC RAND_CONV REDUCE_CONV;

(* Simple ML functions to help find good parameters for the linear
   congruence pseudo-random bit generator.

fun iterate f 0 x = []
  | iterate f n x = x::(iterate f (n - 1) (f x));

fun linear a b n x = (a * x + b) mod (2 * n + 1);

val linear1 = linear 103 95 79;
iterate linear1 200 0;
*)

end;
