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
  type tnn = {opdict: opdict, headnn: nn, dimin: int, dimout: int}
  type dhtnn =
    {opdict: opdict, headeval: nn, headpoli: nn, dimin: int, dimout: int}

  val oper_compare : (term * int) * (term * int) -> order

  (* random generation *)
  val random_headnn : (int * int) -> nn
  val random_opdict : int -> (term * int) list -> opdict
  val random_tnn : (int * int) -> (term * int) list -> tnn
  val random_dhtnn  : (int * int) -> (term * int) list -> dhtnn

  (* I/O *)
  val string_of_tnn : tnn -> string
  val string_of_dhtnn : dhtnn -> string
  val write_dhtnn : string -> dhtnn -> unit
  val read_dhtnn : string -> dhtnn
  
  val write_trainset : string -> 
    (term * real list) list -> unit
  val write_dhtrainset : string -> 
    (term * real list) list * (term * real list) list -> unit
  val read_trainset : string -> 
    (term * real list) list
  val read_dhtrainset : string ->
    (term * real list) list * (term * real list) list
  
  (* inference *)
  val infer_tnn : tnn -> term -> real list

  (* training *)
  val pmb_flag : bool ref
  val pmt_flag : bool ref  

  val train_tnn_schedule :
    (int * int) -> tnn ->
    (term list * vect) list * (term list * vect) list ->
    (int * real) list ->
    tnn

  val train_dhtnn_schedule :
    int -> dhtnn ->
    int -> (term list * vect) list * (term list * vect) list ->
    (int * real) list ->
    dhtnn

  (* prepare the dataset before training *)
  val trainset_info : (term * real list) list -> string

  val prepare_trainset : (term * real list) list -> (term list * vect) list

  val prepare_train_tnn :
    (int * int) -> tnn ->
    (term * real list) list * (term * real list) list ->
    (int * real) list ->
    tnn


end
