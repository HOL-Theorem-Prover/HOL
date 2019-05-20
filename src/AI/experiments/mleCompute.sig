signature mleCompute =
sig

  include Abbrev

  val compute_exout : term list -> (term * real list) list
  val random_tnn_compute : int -> mlTreeNeuralNetwork.tnn 

end
