(* ========================================================================= *)
(* FILE          : mleCompute.sml                                            *)
(* DESCRIPTION   : Direct computation on terms using tree neural network     *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleCompute :> mleCompute =
struct

open HolKernel Abbrev boolLib aiLib psTermGen mlTreeNeuralNetwork

val ERR = mk_HOL_ERR "mleCompute"

(* -------------------------------------------------------------------------
   Add output to examples
   ------------------------------------------------------------------------- *)

fun compute_exout ex = map_snd (bin_rep 4) ex

(* -------------------------------------------------------------------------
   Tree Neural Network
   ------------------------------------------------------------------------- *)

fun random_tnn_compute dim =
  let 
    val operl = mk_fast_set oper_compare (operl_of ``0 + SUC 0 * 0``)
    val nbit = 4
  in
    random_tnn (dim,nbit) operl
  end

(*
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
load "mleArithData"; open mleArithData;
load "mleCompute"; open mleCompute;

val (trainex,validex) = create_allex 200;

val randtnn = random_tnn_compute dim;
val bsize = 64;
val schedule = [200, 0.1 / (Real.fromInt bsize)];
val ncore = 2;
val tnn = prepare_train_tnn (ncore,bsize) randtnn (trainex,first_n 100 
trainex) schedule;

val r1 = accuracy_set tnn trainex;
val r2 = accuracy_set tnn validex;
*)

(* Compute external experiments 
load "smlParallel"; load "mlTune"; load "mleCompute"; 
open mlTreeNeuralNetwork mlTune aiLib smlParallel mleCompute;
load "mlTacticData"; open mlTacticData;

val trainfile = (!parallel_dir) ^ "/train";
val testfile = (!parallel_dir) ^ "/test";
val operlfile = (!parallel_dir) ^ "/operl";
val operl = mk_fast_set oper_compare (operl_of ``0 + SUC 0 * 0``);

val (trainex,validex) = create_allex 200;
export_terml (HOLDIR ^ "/src/AI/experiments/trainex200") (map fst trainex);
export_terml (HOLDIR ^ "/src/AI/experiments/trainex200") (map fst validex);

fun init () =
  (
  write_tnnex trainfile trainex;
  write_tnnex testfile validex;
  write_operl operlfile operl
  )
;
val dl = [16,8];
val nl = [100,200];
val bl = [16,128];
val ll = [10,100];
val yl = [2,3];
fun codel_of wid = tune_codel_of (dl,nl,bl,ll,ml) 1 wid;
val paraml = grid_param (dl,nl,bl,ll,ml);

val ncore = 32;
val (final1,t) = add_time 
  (parmap_queue_extern ncore codel_of (init,tune_collect_result)) paraml;

val final2 = dict_sort compare_rmax final1;
write_param_results 
  (HOLDIR ^ "/src/AI/experiments/mleCompute_param_results_200") final2;
*)








end (* struct *)
