signature mlTune =
sig

  include Abbrev

  type ml_param = 
    {
    dim: int, 
    nepoch: int, 
    batchsize: int, 
    learningrate: real, 
    momentum: real
    }

  val grid_param : int list * int list * int list * int list * int list -> 
    ml_param list

  val train_tnn_param : (int * int) -> int ->
    (term * int) list ->
    (term * real list) list * (term * real list) list ->
    ml_param -> unit

  val tune_codel_of : int -> int -> string list
  val tune_collect_result : int * int -> ml_param * real
     
  val write_param_results : string -> (ml_param * real) list -> unit       

end
