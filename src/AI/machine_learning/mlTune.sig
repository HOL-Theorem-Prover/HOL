signature mlTune =
sig

  include Abbrev

  type ml_param =
    {dim: int, nepoch: int, batchsize: int, learningrate: real, nlayers: int}

  val grid_param : int list * int list * int list * int list * int list ->
    ml_param list

  (* tnn *)
  val train_tnn_param : (int * int) -> int ->
    (term * int) list ->
    (term * real list) list * (term * real list) list ->
    ml_param -> unit
  val tune_codel_of :
    int list * int list * int list * int list * int list ->
    int -> int -> string list
  val tune_collect_result : int * int -> ml_param * (real * real * real)
  val write_param_results :
    string -> (ml_param * (real * real * real )) list -> unit

  (* dhtnn *)
  val train_dhtnn_param : int * int ->
    int -> ('a, 'b) mlReinforce.gamespec ->
    (term * real list * real list) list ->
    ml_param -> unit
  val dhtune_codel_of :
    ('a,'b) mlReinforce.gamespec ->
    int list * int list * int list * int list * int list ->
    int -> int -> string list
  val dhtune_collect_result :
    int * int -> (ml_param * mlTreeNeuralNetwork.dhtnn)


end
