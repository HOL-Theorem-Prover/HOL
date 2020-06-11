signature mlTreeNeuralNetwork =
sig

include Abbrev

  type tnn = (term, mlNeuralNetwork.nn) Redblackmap.dict
  type tnnex = ((term * real list) list) list
  type tnnparam = (term * int list) list
  type schedule = mlNeuralNetwork.schedule
  type tnnbatch = (term list * (term * mlMatrix.vect) list) list
 
  (* initial tnn *)
  val operl_of_term : term -> (term * int) list
  val oper_compare : (term * int) * (term * int) -> order
  val random_tnn : (term * int list) list -> tnn
  val dim_std : int * int -> term -> int list
  val dim_std_arity : int * int -> (term * int) -> int list
  val random_tnn_std : (int * int) -> term list -> tnn
  
  (* examples *)
  val mk_embedding_var : (real vector * hol_type) -> term
  val stats_tnnex : tnnex -> string
  val precomp_embed : tnn -> term -> term
  val prepare_tnnex : tnnex -> tnnbatch
  val nntm_of_goal : goal -> term

  (* I/O *)
  val write_tnn : string -> tnn -> unit
  val read_tnn : string -> tnn
  val write_tnnex : string -> tnnex -> unit
  val read_tnnex : string -> tnnex
  val write_tnnparam : string -> tnnparam -> unit
  val read_tnnparam : string -> tnnparam

  (* inference *)
  val infer_tnn : tnn -> term list -> (term * real list) list 
 
  (* training *)
  val train_tnn_epoch_nopar :
    mlNeuralNetwork.trainparam -> real list -> tnn -> tnnbatch list ->
    tnn * real
  val train_tnn : schedule -> tnn -> tnnex * tnnex -> tnn
  
  (* testing *)
  val is_accurate : tnn -> (term * real list) list -> bool
  val tnn_accuracy : tnn -> tnnex -> real
  
  (* parallellism and tentative to automatically determine hyperparameters *)
  val traintnn_extspec :
    (unit, (tnnex * schedule * tnnparam), tnn) smlParallel.extspec
  val train_tnn_automl : mlNeuralNetwork.trainparam -> tnn -> tnnex -> tnn


end
