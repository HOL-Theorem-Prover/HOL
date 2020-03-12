signature mleArith =
sig

  include Abbrev
 
  type tnn = mlTreeNeuralNetwork.tnn

  val train_fixed : unit -> tnn
  val test_fixed : tnn -> real list

end
