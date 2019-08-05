signature mleCommunicate =
sig

  include Abbrev

  type vect = real vector
  type nnc = mlNeuralNetwork.nn * mlNeuralNetwork.nn
  
  val same_sign : vect -> vect -> bool
  val discretize : vect -> vect

  val all_discrete_inv : int -> vect list
  val train_nnc : (int * int) -> nnc -> (vect * vect) list -> nnc
  val infer_nnc : nnc -> vect -> vect
  val accuracy_nnc : nnc -> (vect * vect) list -> real

end
