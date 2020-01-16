signature mlTreeNeuralNetwork =
sig

include Abbrev

  type tnn = (term, mlNeuralNetwork.nn) Redblackmap.dict
  type tnnex = ((term * real list) list) list
  type tnnparam = (term * int list) list  
  type schedule = mlNeuralNetwork.schedule

  val random_tnn : (term * int list) list -> tnn
  val dim_std : int * int -> term -> int list
  val random_tnn_std : (int * int) -> term list -> tnn
  val mk_embedding_var : real vector -> term 
  
  val write_tnn : string -> tnn -> unit
  val read_tnn : string -> tnn
  val write_tnnex : string -> tnnex -> unit
  val read_tnnex : string -> tnnex
  val write_tnnparam : string -> tnnparam -> unit
  val read_tnnparam : string -> tnnparam

  val infer_tnn : tnn -> term list -> (term * real list) list
  val train_tnn : schedule -> tnn -> tnnex * tnnex -> tnn
  val is_accurate : tnn -> (term * real list) list -> bool
  val tnn_accuracy : tnn -> tnnex -> real

  val traintnn_extspec :
    (unit, (tnnex * schedule * tnnparam), tnn) smlParallel.extspec

end
