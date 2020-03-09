signature mleArith =
sig

  include Abbrev

  type tnn = mlTreeNeuralNetwork.tnn
  val compute_exout : term list -> (term * real list) list
  val train_fixed : unit -> tnn
  val test_fixed : tnn -> real list

end
