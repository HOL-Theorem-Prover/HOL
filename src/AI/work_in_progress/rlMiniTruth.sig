signature rlMiniTruth =
sig
  
  include Abbrev

  val tnn_accuracy : mlTreeNeuralNetwork.treenn -> (term * real) list -> real

  val knn_accuracy : 
    rlLib.knninfo * (term, real) Redblackmap.dict ->
    'a * (term * real) list -> real



end 
