(* ========================================================================= *)
(* FILE          : rlTrain.sml                                               *)
(* DESCRIPTION   : Extract examples form proofs                              *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlMiniTruth :> rlMiniTruth =
struct

(*
  load "mlTreeNeuralNetwork"; load "rlLib"; load "psTermGen";
  load "mlNearestNeighbor";
*)

open HolKernel Abbrev boolLib aiLib rlLib rlMiniEx
mlFeature mlNearestNeighbor mlTreeNeuralNetwork

val ERR = mk_HOL_ERR "rlMiniTruth"

fun tnn_accuracy tnn testset =
  let fun correct (tm,expectv) =
    let val v = eval_treenn tnn tm in
      if expectv > 0.5 then v > 0.5 else v < 0.5
    end
  in
    int_div (length (filter correct testset)) (length testset)
  end

fun knn_accuracy knn (trainset,testset) =
  let fun correct (tm,expectv) =
    let val v = infer_knn knn tm in
      if expectv > 0.5 then v > 0.5 else v < 0.5
    end
  in
    int_div (length (filter correct testset)) (length testset)
  end

(*
load "rlMiniTruth"; open rlLib rlMiniEx rlMiniTruth mlTreeNeuralNetwork;

val (trainset,testset) = data_mg1 ();

(* tree neural network *)
val operl = operl_of_term ``SUC 0 + 0 * 0 = 0``;
val dim = 4;
val randtnn = random_treenn (dim,1) operl;
val tnn = train_tnn_eval dim randtnn (trainset,testset);
val tnnaccuracy = tnn_accuracy tnn testset;

(* nearest neighbor *)
val knndata = train_knn trainset;
val knnaccuracy = knn_accuracy knndata (trainset,testset);
*)

end (* struct *)






