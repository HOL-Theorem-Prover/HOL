signature mleCompute =
sig

  include Abbrev

  val create_allex :  
    int -> (term * real list) list * (term * real list) list
  val stats_ex : (term * 'a) list -> (int * int) list
  val random_tnn_compute : int -> mlTreeNeuralNetwork.tnn 

end
