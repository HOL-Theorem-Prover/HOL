signature tttTrain =
sig

  include Abbrev
  
  type token = tttToken.token
  type tnn =  mlTreeNeuralNetwork.tnn

  val mask_unknown_val : tnn -> term -> term
  val mask_unknown_pol : tnn -> term -> term
  val mask_unknown_arg : tnn -> term -> term
  val nntm_of_stateval : goal -> term
  val nntm_of_statepol : goal * string -> term
  val nntm_of_statearg : (goal * string) * token -> term
  val train_fixed : real -> (term * real list) list list -> tnn

end
