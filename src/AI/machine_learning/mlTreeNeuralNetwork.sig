signature mlTreeNeuralNetwork =
sig

include Abbrev

  type tnn = (term, mlNeuralNetwork.nn) Redblackmap.dict
  type tnnex = ((term * real list) list) list
  type tnndim = (term * int list) list
  type schedule = mlNeuralNetwork.schedule
  type vect = mlMatrix.vect
  type tnnbatch = (term list * (term * vect) list) list

  (* dimension of neural networks *)
  val operl_of_term : term -> (term * int) list
  val oper_compare : (term * int) * (term * int) -> order
  val dim_std_arity : int * int -> (term * int) -> int list
  val dim_std : int * int -> term -> int list

  (* initial tnn *)
  val random_tnn : (term * int list) list -> tnn
  val random_tnn_std : (int * int) -> term list -> tnn

  (* examples *)
  val stats_tnnex : tnnex -> string

  (* I/O *)
  val write_tnn : string -> tnn -> unit
  val read_tnn : string -> tnn
  val write_tnnex : string -> tnnex -> unit
  val read_tnnex : string -> tnnex
  val write_tnndim : string -> tnndim -> unit
  val read_tnndim : string -> tnndim
  val basicex_to_tnnex : (term * real) list -> tnnex

  (* inference *)
  val fp_emb : tnn -> term -> vect list -> vect
  val infer_emb : tnn -> term -> vect
  val infer_tnn : tnn -> term list -> (term * real list) list
  val infer_tnn_basic : tnn -> term -> real


  (* training *)
  val train_tnn : schedule -> tnn -> tnnex * tnnex -> tnn

  (* testing *)
  val is_accurate : tnn -> (term * real list) list -> bool
  val tnn_accuracy : tnn -> tnnex -> real

  (* object for training multiple instance in parallel *)
  val traintnn_extspec :
    (unit, (tnnex * schedule * tnndim), tnn) smlParallel.extspec




end
