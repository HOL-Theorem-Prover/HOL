(* ========================================================================= *)
(* FILE          : mleCompute.sml                                            *)
(* DESCRIPTION   : Direct computation on terms using tree neural network     *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleCompute :> mleCompute =
struct

open HolKernel Abbrev boolLib aiLib psTermGen smlParallel mlTreeNeuralNetwork
mlTacticData mleLib mleArithData

val ERR = mk_HOL_ERR "mleCompute"

val compute_dir = HOLDIR ^ "/src/AI/experiments/data_compute"

(* -------------------------------------------------------------------------
   Examples
   ------------------------------------------------------------------------- *)

fun compute_exout tml = map_assoc (bin_rep 4 o eval_numtm) tml

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

fun train_fixed () =
  let
    val tml = import_terml (dataarith_dir ^ "/train");
    val exl = compute_exout tml
    val operl = mk_fast_set oper_compare (operl_of ``0 + SUC 0 * 0``)
    val tnn_param =
      {dimin = 12, dimout = 4,
       nlayer_headnn = 2, nlayer_oper = 2,
       operl = operl}
    val schedule =
      [{batch_size = 16, learning_rate = 0.02,
        ncore = 4, nepoch = 100, verbose = true}]
    val randtnn = random_tnn tnn_param
    val tnn = train_tnn schedule randtnn (exl,[])
  in
    mkDir_err compute_dir; write_tnn (compute_dir ^ "/tnn") tnn;
    tnn
  end

(* ------------------------------------------------------------------------
   Testing
   ------------------------------------------------------------------------ *)

fun test_fixed tnn =
  let
    val filel = map (fn x => dataarith_dir ^ "/" ^ x) ["train","valid","test"]
    val tmll = map import_terml filel
    val exl = map compute_exout tmll
  in
    map (tnn_accuracy tnn) exl
  end

(*
load "mleCompute"; open mleCompute;
load "mleArithData"; open mleArithData;
val tnn = train_fixed ();
val r = test_fixed tnn;
*)

(* ------------------------------------------------------------------------
   Comparison with nearest neighbor
   ------------------------------------------------------------------------ *)

(*
load "mleCompute"; open mleCompute;
load "mleArithData"; open mleArithData;
load "mlNearestNeighbor"; open mlNearestNeighbor;
load "mlTacticData"; open mlTacticData;

val train = compute_exout (import_terml (dataarith_dir ^ "/train"));
val valid = compute_exout (import_terml (dataarith_dir ^ "/valid"));
val test = compute_exout (import_terml (dataarith_dir ^ "/test"));
val knn = train_knn train;
val validacc = knn_accuracy knn valid;
val testacc = knn_accuracy knn test;
*)


end (* struct *)
