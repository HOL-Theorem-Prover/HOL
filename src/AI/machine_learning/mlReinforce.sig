signature mlReinforce =
sig

  include Abbrev

  val dhtnn_file : unit -> string  

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
    write_targetl: 'a psMCTS.sit list -> unit,
    read_targetl: unit -> 'a psMCTS.sit list,
    opens: string
    }

  (* rl parameters *)
  val ngen_glob : int ref
  val ntarget_compete : int ref    
  val ntarget_explore : int ref
  val level_glob : int ref
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
  val ncore_mcts_glob : int ref

  (* training *)
  val random_dhtnn_gamespec : 
    ('a,'b) gamespec -> mlTreeNeuralNetwork.dhtnn
  val train_dhtnn : 
    ('a,'b) gamespec ->
    (term * real list * real list) list  ->
    mlTreeNeuralNetwork.dhtnn
  
  (* competition *)
  val compete_one : ('a,'b) gamespec -> 
    mlTreeNeuralNetwork.dhtnn -> 'a psMCTS.sit list -> int

  (* generating examples *)
  val rl_startex : ('a,'b) gamespec -> (term * real list * real list) list
  
  (* exploration (search) *)
  val explore_test : ('a,'b) gamespec -> mlTreeNeuralNetwork.dhtnn -> 
    'a psMCTS.sit -> unit
  val explore_extern : ('a,'b) gamespec -> int * int ->
     bool * bool -> mlTreeNeuralNetwork.dhtnn -> 'a psMCTS.sit -> unit

  (* reinforcement learning loop *)
  val logfile_glob : string ref
  val summary : string -> unit
  val start_rl_loop : 
    ('a,'b) gamespec ->
    (term * real list * real list) list * mlTreeNeuralNetwork.dhtnn


end
