(* ========================================================================= *)
(* FILE          : mleCompute.sml                                            *)
(* DESCRIPTION   : Direct computation on terms using tree neural network     *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleCompute :> mleCompute =
struct

open HolKernel Abbrev boolLib aiLib psTermGen smlParallel mlTreeNeuralNetwork
mlTacticData mlTune mleArithData

val ERR = mk_HOL_ERR "mleCompute"

val compute_dir = HOLDIR ^ "/src/AI/experiments/data_compute"

(* -------------------------------------------------------------------------
   Constructing examples
   ------------------------------------------------------------------------- *)

fun compute_exout tml = map_assoc (bin_rep 4 o eval_numtm) tml

(* -------------------------------------------------------------------------
   Associated tree neural network
   ------------------------------------------------------------------------- *)

fun compute_random_tnn dim =
  let
    val operl = mk_fast_set oper_compare (operl_of ``0 + SUC 0 * 0``)
    val nbit = 4
  in
    random_tnn (dim,nbit) operl
  end

(* -------------------------------------------------------------------------
   Training with a fixed set of parameters
   ------------------------------------------------------------------------- *)

fun train_fixed basename trainex =
  let
    val dim = 12
    val randtnn = compute_random_tnn dim
    val bsize = 16
    val schedule = [(400, 0.02 / (Real.fromInt bsize))]
    val ncore = 4
    val tnn = prepare_train_tnn
      (ncore,bsize) randtnn (trainex,first_n 100 trainex) schedule
    val _ = mkDir_err compute_dir
  in
    write_tnn (compute_dir ^ "/" ^ basename) tnn;
    tnn
  end

(* ------------------------------------------------------------------------
   Accuracy of the tree neural network on arithmetical datasets
   ------------------------------------------------------------------------ *)

fun accuracy_fixed tnn =
  let
    val filel = map (fn x => dataarith_dir ^ "/" ^ x)
      ["train","valid","test","big"]
    val tmll = map mlTacticData.import_terml filel
    val exl = map compute_exout tmll
  in
    quadruple_of_list (map (accuracy_set tnn) exl)
  end

(* ------------------------------------------------------------------------
   Tuning parameters by training with external parallelization.
   Does not print the tree neural network yet.
   ------------------------------------------------------------------------ *)

fun parameter_tuning basename ncore ncore_loc =
  let
    val _ = mkDir_err compute_dir
    val traintml = import_terml (dataarith_dir ^ "/train");
    val trainex = compute_exout traintml;
    val fake_testex = first_n 100 trainex
    val trainfile = (!parallel_dir) ^ "/train";
    val testfile = (!parallel_dir) ^ "/test";
    val operlfile = (!parallel_dir) ^ "/operl";
    val operl = mk_fast_set oper_compare (operl_of ``0 + SUC 0 * 0``);
    fun init () =
      (
      write_tnnex trainfile trainex;
      write_tnnex testfile fake_testex;
      write_operl operlfile operl
      )
    val dl = [12,16]
    val nl = [400]
    val bl = [16,64]
    val ll = [10,20,50]
    val yl = [2,4]
    fun codel_of wid = tune_codel_of (dl,nl,bl,ll,yl) ncore_loc wid
    val paraml = grid_param (dl,nl,bl,ll,yl)
    val final =
      parmap_queue_extern ncore codel_of (init,tune_collect_result) paraml
  in
    write_param_results (compute_dir ^ "/" ^ basename) final
  end


end (* struct *)
