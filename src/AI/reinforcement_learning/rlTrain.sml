(* ========================================================================= *)
(* FILE          : rlTrain.sml                                               *)
(* DESCRIPTION   : Extract examples form proofs                              *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlTrain :> rlTrain =
struct

open HolKernel Abbrev boolLib aiLib mlFeature mlNearestNeighbor 
mlTreeNeuralNetwork psMCTS rlLib 

val ERR = mk_HOL_ERR "rlTrain"

(* -------------------------------------------------------------------------
   Training tools
   ------------------------------------------------------------------------- *)

fun list_split ll = case ll of
    [] => []
  | [l] => map (fn x => [x]) l
  | l :: m =>
    let val m' = list_split m in
      map (fn (a,b) => a :: b) (combine (l,m'))
    end

(* todo: how to make the size of the test set constant *)
fun split_traintest percent l =
  let
    val n = Real.floor (percent * Real.fromInt (length l))
    val (train,test) = part_n n (shuffle l)
  in
    (train, filter (fn (x,_) => not (mem x (map fst train))) test)
  end

fun trainset_info_eval trainset =
  if not (null trainset) then 
    let
      val mean = average_real (map snd trainset)
      val dev = standard_deviation (map snd trainset)
    in
      "  length: " ^ int_to_string (length trainset) ^ "\n" ^
      "  mean: " ^ Real.toString mean ^ "\n" ^
      "  deviation: " ^ Real.toString dev
    end
  else "empty testset"

fun trainset_info_poli trainset =
  if not (null trainset) then 
    let
      val splitpoli = list_split (map snd trainset)
      val meanl = map (Real.toString o approx 6 o average_real) splitpoli
      val devl = map (Real.toString o approx 6 o standard_deviation) splitpoli
    in
      "  length: " ^ int_to_string (length trainset) ^ "\n" ^
      "  mean: " ^ String.concatWith " " meanl ^ "\n" ^
      "  deviation: " ^ String.concatWith " " devl
    end
  else "empty testset"

(* -------------------------------------------------------------------------
   Training tree neural network
   ------------------------------------------------------------------------- *)

fun train_tnn_either preparef infof dim randtnn (trainset,testset) =
  if null trainset then (print_endline "empty trainset"; randtnn) else
  let
    val _        = print_endline ("trainset " ^ infof trainset)
    val _        = print_endline ("testset  " ^ infof testset)
    val bsize    = if length trainset < 64 then 1 else 64
    val schedule = [(50,0.1),(50,0.01)]
    val pset  = (preparef trainset, preparef testset)
    val ((tnn,loss), nn_tim) =
      add_time (train_treenn_schedule dim randtnn bsize pset) schedule
  in
    print_endline ("  NN Time: " ^ Real.toString nn_tim);
    print_endline ("  Last loss: " ^ Real.toString loss);
    tnn
  end

fun train_tnn_eval dim randtnn (trainset,testset) =
  train_tnn_either prepare_trainset_eval trainset_info_eval
    dim randtnn (trainset,testset)

fun train_tnn_poli dim randtnn (trainset,testset) =
  train_tnn_either prepare_trainset_poli trainset_info_poli
    dim randtnn (trainset,testset)

(* -------------------------------------------------------------------------
   Training nearest neighbor
   ------------------------------------------------------------------------- *)

type knninfo =
  (int, real) Redblackmap.dict * (term, int list) Redblackmap.dict

fun train_knn trainset =
  let
    val trainfea = map_assoc feahash_of_term (map fst trainset);
    val trainfead = dnew Term.compare trainfea;
    val symweight = learn_tfidf trainfea;
  in
    (* rev for newest first since it might not be a set *)
    ((symweight,trainfead), dnew Term.compare (rev trainset))
  end

fun infer_knn (knninfo,trainsetd) tm =
  let val neartm = hd (termknn knninfo 1 (feahash_of_term tm)) in
    dfind neartm trainsetd (* predicting from the trainset *)
  end

(* -------------------------------------------------------------------------
   Accuracy of a binary classifier    
   ------------------------------------------------------------------------- *)

fun f_accuracy f testset =
  let fun correct (tm,expectv) =
    let val v = f tm in if expectv > 0.5 then v > 0.5 else v < 0.5 end
  in
    int_div (length (filter correct testset)) (length testset)
  end

fun tnn_accuracy tnn testset = f_accuracy (eval_treenn tnn) testset
fun knn_accuracy knn testset = f_accuracy (infer_knn knn) testset

(* Move to rlSupervisedExp

tree-edit distance.
make a dataset see if it can learn the tree edit distance.


load "rlMiniTruth"; open rlLib rlMiniEx rlMiniTruth mlTreeNeuralNetwork;
val (trainset,testset) = data_nboccurSUC ();
val operl = operl_of_term ``SUC 0 + 0 * 0``;
val dim = 4;
val tnn = train_tnn_eval dim (random_treenn (dim,1) operl) (trainset,testset)
val tnnaccuracy = tnn_accuracy tnn testset;
val r = read_nboccur (eval_treenn tnn ``SUC 0 + 0 * 0 ``);
val mat = aiLib.dfind (``x:num``,0) (fst tnn);
*)

end (* struct *)





