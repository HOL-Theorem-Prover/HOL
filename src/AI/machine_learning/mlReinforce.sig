signature mlReinforce =
sig

  include Abbrev

  (* 'a is the type of board, 'b is the type for move *)
  type ('a,'b) gamespec =
    {
    movel : 'b list,
    move_compare : 'b * 'b -> order,
    string_of_move : 'b -> string,
    filter_sit : 'a psMCTS.sit -> (('b * real) list -> ('b * real) list),
    status_of : ('a psMCTS.sit -> psMCTS.status),
    apply_move : ('b -> 'a psMCTS.sit -> 'a psMCTS.sit),
    operl : (term * int) list,
    nntm_of_sit: 'a psMCTS.sit -> term,
    mk_targetl: int -> int -> 'a psMCTS.sit list,
    write_targetl: string -> 'a psMCTS.sit list -> unit,
    read_targetl: string -> 'a psMCTS.sit list,
    opens: string,
    max_bigsteps : 'a psMCTS.sit -> int
    }
  type dhex = (term * real list * real list) list
  type dhtnn = mlTreeNeuralNetwork.dhtnn
  type flags = bool * bool * bool

  (* rl parameters *)
  val ngen_glob : int ref
  val ntarget_compete : int ref
  val ntarget_explore : int ref
  val level_glob : int ref
  val level_threshold : real ref
  (* nn parameters *)
  val exwindow_glob : int ref
  val uniqex_flag : bool ref
  val lr_glob : real ref
  val dim_glob : int ref
  val batchsize_glob : int ref
  val nepoch_glob : int ref
  val ncore_train_glob : int ref
  (* mcts parameters *)
  val nsim_glob : int ref
  val decay_glob : real ref
  val temp_flag : bool ref
  val ncore_mcts_glob : int ref

  val eval_dir : string

  (* mcts *)
  val mcts_gamespec_dhtnn : 
    int -> ('a,'b) gamespec -> dhtnn -> 'a psMCTS.sit -> ('a,'b) psMCTS.tree

  (* training *)
  val random_dhtnn_gamespec :
    ('a,'b) gamespec -> dhtnn
  val train_dhtnn :
    ('a,'b) gamespec ->
    (term * real list * real list) list  ->
    mlTreeNeuralNetwork.dhtnn

  (* exploration *)
  val explore_test : ('a,'b) gamespec -> mlTreeNeuralNetwork.dhtnn ->
    'a psMCTS.sit -> ('a,'b) psMCTS.node list
  
  (* external parallel exploration specification *)
  val mk_extspec : string -> ('a,'b) gamespec ->
    (flags * dhtnn, 'a psMCTS.sit, bool * dhex) smlParallel.extspec

  (* reinforcement learning loop *)
  val logfile_glob : string ref
  val summary : string -> unit
  val start_rl_loop :
    ('a,'b) gamespec * 
    (flags * dhtnn, 'a psMCTS.sit, bool * dhex) smlParallel.extspec ->
    dhex * dhtnn


end
