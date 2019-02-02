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

  (* printing *)
  val string_of_tnn : tnn -> string
  val string_of_trainset : (term * real list) list -> string

  (* inference *)
  val infer_tnn : tnn -> term -> real list

  (* training *)
  val adaptive_flag : bool ref
  
  val train_tnn_schedule :
    tnn -> 
    int -> (term list * vect) list * (term list * vect) list ->
    (int * real) list ->
    tnn

  val train_dhtnn_schedule : 
    dhtnn -> 
    int -> (term list * vect) list * (term list * vect) list ->
    (int * real) list -> 
    dhtnn
  
  (* prepare the dataset before training *)
  val trainset_info : (term * real list) list -> string

  val prepare_trainset : (term * real list) list -> (term list * vect) list  

  val prepare_train_tnn :
    tnn -> 
    int -> (term * real list) list * (term * real list) list ->
    (int * real) list ->
    tnn


end
