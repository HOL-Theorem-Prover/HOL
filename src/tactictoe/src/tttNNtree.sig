signature tttNNtree =
sig

include Abbrev

  type layer =
    {a  : real -> real, 
     da : real -> real,
     w  : real vector vector} 

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
  val random_headnn : int -> nn
  val random_opdict : int -> (term * int) list -> opdict
  val random_treenn : int -> (term * int) list -> treenn
  
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
  val prepare_trainset   : 
    (term * (real * real list)) list -> (term list * real vector) list
  val prepare_trainsetone : 
    (term * real) list -> (term list * real vector) list
  val cal_of_prepset     : 
    (term list * real vector) list -> (term * int) list
  
  (* inference *)
  val eval_treenn       : treenn -> term -> real

  (* training *)
  val train_treenn_schedule : 
    int -> treenn -> int ->
    (term list * real vector) list ->
    (int * real) list ->
    (treenn * real)

  (* printing *)
  val string_of_treenn      : treenn -> string
  val string_of_trainset    : (term * (real * real list)) list -> string
  val string_of_trainsetone : (term * real) list -> string  

  (* input terms *)
  val goal_to_nnterm     : goal -> term
  val goallist_to_nnterm : goal list -> term
  val forget_to_nnterm   : (goal * term) -> term
  val cut_to_nnterm      : (goal * term) -> term
  val cutpos_to_nnterm   : (goal * term) -> term
  val initcut_to_nnterm  : (goal * term) -> term
  val buildcut_to_nnterm : ((goal * term) * term) -> term
  val goalchoice_to_nnterm : (goal list * goal) -> term

  (* operators *)
  val operl_of_term : term -> (term * int) list

end
