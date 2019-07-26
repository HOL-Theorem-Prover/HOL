signature mlTreeNeuralNetwork =
sig

include Abbrev

  (* globals *)
  val nlayer_glob : int ref

  (* types *)
  type vect = real vector
  type mat = real vector vector
  type layer = {a  : real -> real, da : real -> real, w : mat}
  type nn = layer list
  type fpdata = {layer : layer, inv : vect, outv : vect, outnv : vect}
  type bpdata = {doutnv : vect, doutv  : vect, dinv : vect, dw : mat}
  type opdict = ((term * int),nn) Redblackmap.dict
  type tnnex = (term * real list) list
  type tnn = {opdict: opdict, headnn: nn, dimin: int, dimout: int}
  type dhex = (term * real list * real list) list  
  type dhtnn =
    {opdict: opdict, headeval: nn, headpoli: nn, dimin: int, dimout: int}
  
  (* random generation *)
  val random_headnn : (int * int) -> nn
  val random_opdict : int -> (term * int) list -> opdict
  val random_tnn : (int * int) -> (term * int) list -> tnn
  val random_dhtnn  : (int * int) -> (term * int) list -> dhtnn

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

  (* inference *)
  val infer_tnn : tnn -> term -> real list
  val infer_tnn_nohead : tnn -> term -> real list (* for debugging *)
  val infer_dhtnn : dhtnn -> term -> real * real list

  (* training *)
  val train_tnn :
    (int * int) -> tnn -> tnnex * tnnex -> (int * real) list -> tnn
  val train_dhtnn :
    (int * int) -> dhtnn -> dhex -> (int * real) list -> dhtnn
 
  (* statistics *)
  val tnn_accuracy : tnn -> (term * real list) list -> real

end
