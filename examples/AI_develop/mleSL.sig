signature mleSL =
sig

  include Abbrev

  type tnn = mlTreeNeuralNetwork.tnn
  datatype move = Incr | Decr | Still
  val vhead : term
  val varl : term list
  val lookahead_all : tnn * (real * int) -> tnn * (real * int)

end
