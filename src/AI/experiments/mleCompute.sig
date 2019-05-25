signature mleCompute =
sig

  include Abbrev

  val compute_exout : term list -> (term * real list) list
  val train_fixed : string -> (term * real list) list -> mlTreeNeuralNetwork.tnn
  val accuracy_fixed : mlTreeNeuralNetwork.tnn -> (real * real * real * real)
  val parameter_tuning : string -> int -> unit

end
