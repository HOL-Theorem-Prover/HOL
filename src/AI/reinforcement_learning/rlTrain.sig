signature rlTrain =
sig

  include Abbrev

  (* Training set *)
  type allex = {
    tacevalex : (term * real) list,
    tacpoliex : (term * real list) list,
    stopevalex : (term * real) list,
    stoppoliex : (term * real list) list,
    lrevalex : (term * real) list,
    lrpoliex : (term * real list) list,
    imitevalex : (term * real) list,
    imitpoliex : (term * real list) list,
    conjunctevalex : (term * real) list,
    conjunctpoliex : (term * real list) list
    }
  val empty_allex : allex

  val add_simulex : (rlRules.board,rlRules.move) psMCTS.tree * allex -> allex

  val discard_oldex : allex -> int -> allex

  (* Neural networks *)
  type alltnn =
    {
    taceval : mlTreeNeuralNetwork.treenn,
    tacpoli : mlTreeNeuralNetwork.treenn,
    stopeval : mlTreeNeuralNetwork.treenn,
    stoppoli : mlTreeNeuralNetwork.treenn,
    lreval : mlTreeNeuralNetwork.treenn,
    lrpoli : mlTreeNeuralNetwork.treenn,
    imiteval : mlTreeNeuralNetwork.treenn,
    imitpoli : mlTreeNeuralNetwork.treenn,
    conjuncteval : mlTreeNeuralNetwork.treenn,
    conjunctpoli : mlTreeNeuralNetwork.treenn
    }
  val random_alltnn : int -> (term * int) list -> alltnn

  (* Training *)
  val train_tnn_eval :
    int -> mlTreeNeuralNetwork.treenn -> (term * real) list ->
    mlTreeNeuralNetwork.treenn

  val train_tnn_poli :
    int -> mlTreeNeuralNetwork.treenn -> (term * real list) list ->
    mlTreeNeuralNetwork.treenn

  val all_train : int -> (term * int) list -> allex -> alltnn


end
