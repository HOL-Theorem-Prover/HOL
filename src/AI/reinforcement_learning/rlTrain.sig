signature rlTrain =
sig

  include Abbrev

  (* tool *)
  val split_traintest :
    real -> (''a * 'b) list -> (''a * 'b) list * (''a * 'b) list

  (* tree neural network *)
  val train_tnn_eval : int ->
    mlTreeNeuralNetwork.treenn -> (term * real) list * (term * real) list ->
    mlTreeNeuralNetwork.treenn
  val train_tnn_poli : int ->
    mlTreeNeuralNetwork.treenn ->
    (term * real list) list * (term * real list) list ->
    mlTreeNeuralNetwork.treenn

  (* nearest neighbor *)
  type knninfo = (int, real) Redblackmap.dict * (term, int list) Redblackmap.dict
  val train_knn : (term * 'a) list -> (knninfo *  (term, 'a) Redblackmap.dict)
  val infer_knn : (knninfo *  (term, 'a) Redblackmap.dict) -> term -> 'a

  (* binary classification accuracy *) 
  val tnn_accuracy : 
    mlTreeNeuralNetwork.treenn -> (term * real) list -> real
  val knn_accuracy :
    knninfo * (term, real) Redblackmap.dict -> (term * real) list -> real


end
