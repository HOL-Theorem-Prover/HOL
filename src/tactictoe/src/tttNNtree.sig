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
  type treenn = ((term,nn) Redblackmap.dict * nn)

  (* preparing training set *)
  val order_subtm : term -> term list  

  (* initialization of the treenn *)
  val random_treenn : int -> (term * int) list -> int -> treenn
  
  (* forward and backward propagation *)
  val fp_treenn : treenn -> term list ->
    (term, fpdata list) Redblackmap.dict * fpdata list

  val bp_treenn : 
    int ->
    (term, fpdata list) Redblackmap.dict * fpdata list ->
    term list * real vector ->
    (term, bpdata list list) Redblackmap.dict * bpdata list
  
  (* training *)
  val train_treenn_nepoch : 
    int -> int -> treenn -> int ->
    (term list * real vector) list ->
    treenn

  (* printing *)
  val string_of_treenn : treenn -> string

end
