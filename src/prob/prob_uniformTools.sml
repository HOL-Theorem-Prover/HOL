(* ------------------------------------------------------------------------- *)
(* A simpset for the canonicalisation procedure.                             *)
(* ------------------------------------------------------------------------- *)

(* non-interactive mode
*)
structure prob_uniformTools :> prob_uniformTools =
struct

open HolKernel Parse boolLib;

(* interactive mode
if !show_assums then () else
 (load "bossLib";
  load "reduceLib";
  load "prob_pseudoTools";
  load "prob_uniformTheory";
  show_assums := true);
*)

open Drule bossLib PairedLambda reduceLib
     prob_pseudoTools prob_uniformTheory;

infix 1 THENC
infix 0 ORELSEC;

val FST_CONV = RATOR_CONV o RAND_CONV;
val SND_CONV = RAND_CONV;
val BETA_PAIR_CONV = DEPTH_CONV GEN_BETA_CONV;

fun UNIF_CONV tm
  = (RATOR_CONV REDUCE_CONV
     THENC (RATOR_CONV (RAND_CONV Num_conv.num_CONV) ORELSEC ALL_CONV)
     THENC (REWR_CONV (CONJUNCT1 unif_def) ORELSEC
            REWR_CONV (CONJUNCT2 unif_def)
            THENC REWR_CONV LET_THM
            THENC RAND_CONV UNIF_CONV
            THENC BETA_PAIR_CONV
            THENC FST_CONV(RATOR_CONV(RATOR_CONV (RAND_CONV (SHD_PSEUDO_CONV)))
                            THENC COND_CONV THENC REDUCE_CONV)
            THENC SND_CONV STL_PSEUDO_CONV)) tm;

fun UNIFORM_CONV tm
  = ((RATOR_CONV (RATOR_CONV (RAND_CONV Num_conv.num_CONV)) ORELSEC ALL_CONV)
     THENC (RATOR_CONV (RAND_CONV Num_conv.num_CONV) ORELSEC ALL_CONV)
     THENC (REWR_CONV (CONJUNCT1 uniform_def) ORELSEC
            REWR_CONV (CONJUNCT2 uniform_def)
            THENC REWR_CONV LET_THM
            THENC RAND_CONV UNIF_CONV
            THENC BETA_PAIR_CONV
            THENC RATOR_CONV (RATOR_CONV (RAND_CONV REDUCE_CONV))
            THENC COND_CONV
            THENC (UNIFORM_CONV ORELSEC ALL_CONV))) tm;

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

Count.apply (UNIFORM ``10:num`` ``10:num``) ``pseudo 0``;
Count.apply (UNIFORML 30 ``10:num`` ``17:num``) ``pseudo 0``;
*)

(* non-interactive mode
*)
end;
