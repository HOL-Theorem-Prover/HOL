(* ------------------------------------------------------------------------- *)
(* Coversions for evaluating the pseudo-random number generator.             *)
(* ------------------------------------------------------------------------- *)

(* non-interactive mode
*)
structure prob_pseudoTools :> prob_pseudoTools =
struct

open HolKernel Parse boolLib;

(* interactive mode
if !show_assums then () else
 (load "bossLib";
  load "reduceLib";
  load "prob_pseudoTheory";
  show_assums := true);
*)

open Drule bossLib reduceLib prob_pseudoTheory;

infix 1 THENC
infix 0 ORELSEC;

val PSEUDO_LINEAR_HD_CONV
  = RATOR_CONV (REWR_CONV pseudo_linear_hd_def)
    THENC REDUCE_CONV;

val PSEUDO_LINEAR_TL_CONV
  = REWR_CONV pseudo_linear_tl_def
    THENC REDUCE_CONV;

val SHD_PSEUDO_LINEAR1_CONV
  = REWR_CONV (CONJUNCT1 pseudo_linear1_def)
    THENC PSEUDO_LINEAR_HD_CONV;

val STL_PSEUDO_LINEAR1_CONV
  = REWR_CONV (CONJUNCT2 pseudo_linear1_def)
    THENC RAND_CONV PSEUDO_LINEAR_TL_CONV;

val SHD_PSEUDO_CONV
  = RAND_CONV (RATOR_CONV (REWR_CONV pseudo_def))
    THENC SHD_PSEUDO_LINEAR1_CONV;

val STL_PSEUDO_CONV
  = RAND_CONV (RATOR_CONV (REWR_CONV pseudo_def))
    THENC STL_PSEUDO_LINEAR1_CONV
    THENC RATOR_CONV (REWR_CONV (SYM pseudo_def));

(*
fun iterate f 0 x = []
  | iterate f n x = x::(iterate f (n - 1) (f x));

fun linear a b n x = (a * x + b) mod (2 * n + 1);

val linear1 = linear 103 95 79;
iterate linear1 200 0;
*)

(* non-interactive mode
*)
end;
