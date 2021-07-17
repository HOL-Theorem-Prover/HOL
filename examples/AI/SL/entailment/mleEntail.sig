signature mleEntail =
sig

  include Abbrev
  type tnn = mlTreeNeuralNetwork.tnn

  val import_entaildata : int -> string -> ((term * real list) list) list

  val train_fixed : unit -> tnn
  val test_fixed : mlTreeNeuralNetwork.tnn -> real list

end
