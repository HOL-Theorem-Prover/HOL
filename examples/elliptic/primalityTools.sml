(* ========================================================================= *)
(* A NAIVE PRIMALITY CHECKER                                                 *)
(* ========================================================================= *)

structure primalityTools :> primalityTools =
struct

open HolKernel Parse boolLib bossLib;

val prime_checker_conv = REWR_CONV primalityTheory.prime_checker THENC EVAL;

end
