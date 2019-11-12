signature mlTreeNeuralNetwork =
sig

include Abbrev

  type vect = real vector
  type mat = real vector vector
  type layer = {a  : real -> real, da : real -> real, w : mat}
  type nn = layer list
  type fpdata = {layer : layer, inv : vect, outv : vect, outnv : vect}
  type bpdata = {doutnv : vect, doutv  : vect, dinv : vect, dw : mat}
  type opdict = ((term * int),nn) Redblackmap.dict
  
  type tnnex = (term * real list) list
  type tnn_param =
    {
    operl: (term * int) list,
    nlayer_oper: int, nlayer_headnn: int,
    dimin: int, dimout: int
    }
  type tnn = {opdict: opdict, headnn: nn, dimin: int, dimout: int}
  
  type dhex = (term * real list * real list) list
  type dhtnn_param =
    {
    operl: (term * int) list,
    nlayer_oper: int, nlayer_headeval: int, nlayer_headpoli: int,
    dimin: int, dimpoli: int
    }
  type dhtnn =
    {opdict: opdict, headeval: nn, headpoli: nn, dimin: int, dimpoli: int}
  
  type schedule = mlNeuralNetwork.train_param list
  
  (* hack for fixed embeddings *)
  val tnn_numvar_prefix : string
  
  (* random generation *)
  val random_tnn : tnn_param -> tnn
  val random_dhtnn  : dhtnn_param -> dhtnn

  (* input/output *)
  val string_of_tnn : tnn -> string
  val write_tnn : string -> tnn -> unit
  val read_tnn : string -> tnn
  val string_of_dhtnn : dhtnn -> string
  val write_dhtnn : string -> dhtnn -> unit
  val read_dhtnn : string -> dhtnn
  val write_dhex : string -> dhex -> unit
  val read_dhex : string -> dhex
  val write_tnnex : string -> tnnex -> unit
  val read_tnnex  : string -> tnnex
  val write_operl : string -> (term * int) list -> unit
  val read_operl  : string -> (term * int) list
  val write_dhtnnparam : string -> dhtnn_param -> unit
  val read_dhtnnparam : string -> dhtnn_param  

  (* inference *)
  val infer_tnn : tnn -> term -> real list
  val infer_tnn_nohead : tnn -> term -> real list (* for debugging *)
  val infer_dhtnn : dhtnn -> term -> real * real list

  (* training *)
  val train_tnn : schedule -> tnn -> tnnex * tnnex -> tnn
  val train_dhtnn : schedule -> dhtnn -> dhex -> dhtnn

  (* statistics *)
  val tnn_accuracy : tnn -> (term * real list) list -> real

end
