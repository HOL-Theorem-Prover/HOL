(* ------------------------------------------------------------------------- *)
(* A conversion to evaluate uniform random numbers.                          *)
(* ------------------------------------------------------------------------- *)

structure prob_uniformTools :> prob_uniformTools =
struct
open HolKernel Parse boolLib;

open Drule bossLib PairedLambda reduceLib prob_pseudoTools prob_uniformTheory;

infix 1 THENC
infix 0 ORELSEC;

val FST_CONV = RATOR_CONV o RAND_CONV;
val SND_CONV = RAND_CONV;
val BETA_PAIR_CONV = DEPTH_CONV GEN_BETA_CONV;

fun PROB_UNIF_CONV tm =
  (RATOR_CONV REDUCE_CONV THENC
   (RATOR_CONV (RAND_CONV Num_conv.num_CONV) ORELSEC ALL_CONV) THENC
   (REWR_CONV (CONJUNCT1 prob_unif_def) ORELSEC
    REWR_CONV (CONJUNCT2 prob_unif_def) THENC
    REWR_CONV LET_THM THENC
    RAND_CONV PROB_UNIF_CONV THENC
    BETA_PAIR_CONV THENC
    FST_CONV
    (RATOR_CONV (RATOR_CONV (RAND_CONV (PROB_PSEUDO_SHD_CONV))) THENC
     COND_CONV THENC REDUCE_CONV) THENC
    SND_CONV PROB_PSEUDO_STL_CONV)) tm;

fun PROB_UNIFORM_CUT_CONV tm =
  ((RATOR_CONV (RATOR_CONV (RAND_CONV Num_conv.num_CONV)) ORELSEC
    ALL_CONV) THENC
   (RATOR_CONV (RAND_CONV Num_conv.num_CONV) ORELSEC ALL_CONV) THENC
   (REWR_CONV (CONJUNCT1 prob_uniform_cut_def) ORELSEC
    REWR_CONV (CONJUNCT2 prob_uniform_cut_def) THENC
    REWR_CONV LET_THM THENC RAND_CONV PROB_UNIF_CONV THENC
    BETA_PAIR_CONV THENC
    RATOR_CONV (RATOR_CONV (RAND_CONV REDUCE_CONV)) THENC
    COND_CONV THENC
    (PROB_UNIFORM_CUT_CONV ORELSEC ALL_CONV))) tm;

(*
fun UNIFORM t n seq
  = UNIFORM_CONV (list_mk_comb (``uniform``, [t, n, seq]));

fun UNIFORML 0 _ _ _ = []
  | UNIFORML m t n seq
  = let val th = UNIFORM t n seq
        val seq' = (snd o dest_comb o snd o dest_eq o concl) th
    in th::UNIFORML (m - 1) t n seq'
    end;

local open computeLib
      val compset = initial_rws ()
      val _ = add_thms [UNIF_DEF_ALT, UNIFORM_DEF_ALT, pseudo_linear1_def,
                        pseudo_def,
                        pseudo_linear_hd_def, pseudo_linear_tl_def] compset
in val EVAL = CBV_CONV compset
end

fun UNIFORM t n seq
  = EVAL (list_mk_comb (``uniform``, [t, n, seq]));

fun UNIFORML 0 _ _ _ = []
  | UNIFORML m t n seq
  = let val th = UNIFORM t n seq
        val seq' = (snd o dest_comb o snd o dest_eq o concl) th
    in th::UNIFORML (m - 1) t n seq'
    end;

Count.apply (UNIFORM ``10:num`` ``10:num``) ``prob_pseudo 0``;
Count.apply (UNIFORML 30 ``10:num`` ``17:num``) ``prob_pseudo 0``;
*)

end;
