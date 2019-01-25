signature mlTreeNeuralNetwork =
sig

include Abbrev

  type layer = {a  : real -> real, da : real -> real, w : real vector vector}
  type nn = layer list

  type fpdata =
    {layer : layer,
     inv   : real vector,
     outv  : real vector,
     outnv : real vector}

  type bpdata =
    {doutnv : real vector,
     doutv  : real vector,
     dinv   : real vector,
     dw     : real vector vector}

  (* Tree NN *)
  type opdict = ((term * int),nn) Redblackmap.dict
  type treenn = opdict * nn

  (* initialization of the treenn *)
  val random_headnn : (int * int) -> nn
  val random_opdict : int -> (term * int) list -> opdict
  val random_treenn : (int * int) -> (term * int) list -> treenn

  (* forward and backward propagation *)
  val fp_treenn : treenn -> term list ->
    (term, fpdata list) Redblackmap.dict * fpdata list

  val bp_treenn :
    int ->
    (term, fpdata list) Redblackmap.dict * fpdata list ->
    term list * real vector ->
    (term * int, bpdata list list) Redblackmap.dict * bpdata list

  (* training set *)
  val add_bias    : real vector -> real vector
  val order_subtm : term -> term list
  val norm_vect   : real vector -> real vector
  val denorm_vect : real vector -> real vector
  val prepare_trainset_poli   :
    (term * real list) list -> (term list * real vector) list
  val prepare_trainset_eval :
    (term * real) list -> (term list * real vector) list

  (* inference *)
  val poli_treenn : treenn -> term -> real list
  val eval_treenn : treenn -> term -> real

  (* training *)
  val train_treenn_schedule :
    int -> treenn -> int ->
    (term list * real vector) list * (term list * real vector) list ->
    (int * real) list ->
    (treenn * real)

  (* printing *)
  val string_of_treenn : treenn -> string
  val string_of_trainset_poli : (term * real list) list -> string
  val string_of_trainset_eval : (term * real) list -> string

end
