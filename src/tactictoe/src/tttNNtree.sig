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
  type treenn = ((term * int),nn) Redblackmap.dict * nn

  (* initialization of the treenn *)
  val random_treenn : (int * int) -> (term * int) list -> treenn
  
  (* forward and backward propagation *)
  val fp_treenn : treenn -> term list ->
    (term, fpdata list) Redblackmap.dict * fpdata list

  val bp_treenn : 
    int ->
    (term, fpdata list) Redblackmap.dict * fpdata list ->
    term list * real vector ->
    (term * int, bpdata list list) Redblackmap.dict * bpdata list
  
  (* inference *)
  val apply_treenn : treenn -> term -> (real * real list)
   
  (* training set *)
  val order_subtm : term -> term list 
  val prepare_trainset   : 
    (term * (real * real list)) list -> (term list * real vector) list
  val cal_of_prepset     : 
    (term list * real vector) list -> (term * int) list
  val string_of_trainset : 
    (term * (real * real list)) list -> string

  (* training *)
  val train_treenn_nepoch : 
    int -> int -> treenn -> int ->
    (term list * real vector) list ->
    treenn

  val train_treenn_schedule : 
    int -> treenn -> int ->
    (term list * real vector) list ->
    (int * real) list ->
    treenn

  (* printing *)
  val string_of_treenn : treenn -> string

  (* training set helpers *)
  val create_boolcastl : term list -> term list
  val cast_to_bool     : term list -> term -> term
  val io_to_nnterm     : term * term -> term
  val goal_to_nnterm   : goal -> term
  val cut_to_nntml     : term list -> (goal * term) -> term list
  val cal_of_term      : term -> (term * int) list

end
