signature mleCompute =
sig

  include Abbrev

  val compute_exout : term list -> (term * real list) list
  val compute_random_tnn : int -> mlTreeNeuralNetwork.tnn
  val train_fixed : string -> (term * real list) list -> mlTreeNeuralNetwork.tnn
  val accuracy_fixed : mlTreeNeuralNetwork.tnn -> (real * real * real * real)
  val parameter_tuning : string -> int -> int -> unit

end
