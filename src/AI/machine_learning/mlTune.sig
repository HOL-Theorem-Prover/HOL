signature mlTune =
sig

  include Abbrev

  (* parameters *)
  type ml_param =
    {dim: int, nepoch: int, batchsize: int, learningrate: real, nlayer: int}

  val grid_param : int list * int list * int list * int list * int list ->
    ml_param list

  (* I/O *)
  val read_paraml : unit -> ml_param list
  val read_state : unit ->
    (term * real list) list * (term * real list) list *
    (term * int) list
  val train_tnn_extern :
    (int * int) *
      ((term * real list) list * (term * real list) list *
      (term * int) list) ->
    int * int -> ml_param -> unit


  (* training function *)
  val train_tnn_parallel :
    int ->
     (int * int) *
     ((term * real list) list * (term * real list) list *
     (term * int) list) ->
    ml_param list -> (real * real * real) list

  (* statistics *)
  val write_param_results :
    string -> (ml_param * (real * real * real )) list -> unit

end
