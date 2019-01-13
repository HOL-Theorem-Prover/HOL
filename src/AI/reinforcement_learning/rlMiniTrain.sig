signature rlMiniTrain =
sig

  include Abbrev

  (* Examples *)
  type allex = {
    stopevalex : (term * real) list,
    stoppoliex : (term * real list) list,
    lrevalex : (term * real) list,
    lrpoliex : (term * real list) list,
    subevalex : (term * real) list,
    subpoliex : (term * real list) list
    }
  val empty_allex : allex
  val add_simulex :
    (rlMiniRules.board,rlMiniRules.move) psMCTS.tree * allex -> allex
  val discard_oldex : allex -> int -> allex

  (* Tree neural network *)
  type alltnn =
    {
    stopeval : mlTreeNeuralNetwork.treenn,
    stoppoli : mlTreeNeuralNetwork.treenn,
    lreval : mlTreeNeuralNetwork.treenn,
    lrpoli : mlTreeNeuralNetwork.treenn,
    subeval : mlTreeNeuralNetwork.treenn,
    subpoli : mlTreeNeuralNetwork.treenn
    }
  val random_alltnn : int -> (term * int) list -> alltnn
  val train_alltnn : int -> (term * int) list -> allex -> alltnn

  (* Nearest neighbor *)
  type allknn =
    {
    stopevalk : (rlLib.knninfo * (term, real) Redblackmap.dict),
    stoppolik : (rlLib.knninfo * (term, real list) Redblackmap.dict),
    lrevalk : (rlLib.knninfo * (term, real) Redblackmap.dict),
    lrpolik : (rlLib.knninfo * (term, real list) Redblackmap.dict),
    subevalk : (rlLib.knninfo * (term, real) Redblackmap.dict),
    subpolik : (rlLib.knninfo * (term, real list) Redblackmap.dict)
    }
  val train_allknn : allex -> allknn

end
