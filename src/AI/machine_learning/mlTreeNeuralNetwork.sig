signature mlTreeNeuralNetwork =
sig

include Abbrev

  type tnn = (term, mlNeuralNetwork.nn) Redblackmap.dict
  val random_tnn : (term * int list) list -> tnn
  val mk_embedding_var : real vector -> term 
  val write_tnn : string -> tnn -> unit
  val read_tnn : string -> tnn
  
  type tnnex = (term list * real list) list
  val write_tnnex : string -> tnnex -> unit
  val read_tnnex : string -> tnnex
  
  val infer_tnn : tnn -> term list -> real list
  val train_tnn : mlNeuralNetwork.schedule -> tnn -> tnnex * tnnex -> tnn
  val tnn_accuracy : tnn -> (term list * real list) list -> real

end
