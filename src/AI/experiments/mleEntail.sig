signature mleEntail =
sig

  include Abbrev

  val entail_dir : string
  val parse_ex : string -> term * real list
  val read_true_exl : string -> term list
  val read_false_exl : string -> term list
  val exprimed_from_file : int -> string -> (term * real list) list
  val entail_random_tnn : int -> mlTreeNeuralNetwork.tnn
  val train_fixed : string -> real
  val accuracy_fixed : mlTreeNeuralNetwork.tnn -> real list

end
