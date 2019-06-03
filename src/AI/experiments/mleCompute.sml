(* ========================================================================= *)
(* FILE          : mleCompute.sml                                            *)
(* DESCRIPTION   : Direct computation on terms using tree neural network     *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleCompute :> mleCompute =
struct

open HolKernel Abbrev boolLib aiLib psTermGen smlParallel mlTreeNeuralNetwork
mlTacticData mlTune mleLib mleArithData

val ERR = mk_HOL_ERR "mleCompute"

val compute_dir = HOLDIR ^ "/src/AI/experiments/data_compute"

(* -------------------------------------------------------------------------
   Constructing examples
   ------------------------------------------------------------------------- *)

fun compute_exout tml = map_assoc (bin_rep 4 o eval_numtm) tml

(* -------------------------------------------------------------------------
   Associated tnn
   ------------------------------------------------------------------------- *)

val operl = mk_fast_set oper_compare (operl_of ``0 + SUC 0 * 0``)

(* -------------------------------------------------------------------------
   Training with a fixed set of parameters
   ------------------------------------------------------------------------- *)

fun train_fixed basename trainex =
  let
    val dim = 12
    val randtnn = random_tnn (dim,4) operl
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

fun parameter_tuning basename ncore =
  let
    val _ =
      parallel_dir := HOLDIR ^ "/src/AI/sml_inspection/parallel_" ^ basename
    val traintml = import_terml (dataarith_dir ^ "/train");
    val trainex = compute_exout traintml;
    val testex = first_n 100 trainex;
    val paraml = grid_param ([12],[100],[16],[20,50,100,200],[2])
    val final = train_tnn_parallel ncore ((1,4),(trainex,testex,operl)) paraml
  in
    mkDir_err compute_dir;
    write_param_results (compute_dir ^ "/" ^ basename) (combine (paraml,final))
  end

end (* struct *)
