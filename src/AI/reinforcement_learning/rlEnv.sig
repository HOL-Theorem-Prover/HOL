signature rlEnv =
sig

  include Abbrev

  (* 'a is the type of board
     ''b is the type for move
     'c is the type of targets *)

  (* rl parameters *)
  val ngen_glob : int ref
  val ntarget_compete : int ref    
  val ntarget_explore : int ref
  (* nn parameters *)
  val exwindow_glob : int ref
  val dim_glob : int ref
  val batchsize_glob : int ref 
  (* mcts parameters *)
  val nsim_glob : int ref
  val decay_glob : real ref
  val ncore_glob : int ref  

  (* adaptative difficulty *)
  val level_glob : int ref

  (* external calls *)
  val mcts_gencode : int -> unit
  val create_savestate : unit -> unit
  val parmap_ext : mlTreeNeuralNetwork.dhtnn -> int -> unit
  val test : int list -> int -> bool -> int -> real list


  (* *)
  type ('a,''b,'c) gamespec =
    {
    movel : ''b list,
    string_of_move : ''b -> string,
    filter_sit : 'a psMCTS.sit -> ((''b * real) list -> (''b * real) list),
    status_of : ('a psMCTS.sit -> psMCTS.status),
    apply_move : (''b -> 'a psMCTS.sit -> 'a psMCTS.sit),
    operl : (term * int) list,
    nntm_of_sit: 'a psMCTS.sit -> term
    }

  val mcts_ext : string -> mlTreeNeuralNetwork.dhtnn -> 
     (rlGameArithGround.board, ''a, 'b) gamespec
               -> rlGameArithGround.board psMCTS.sit -> unit

  val random_dhtnn_gamespec : 
    (rlGameArithGround.board, ''a, 'b) gamespec -> mlTreeNeuralNetwork.dhtnn

  val logfile_glob : string ref
  val summary : string -> unit

  val start_rl_loop : 
    (rlGameArithGround.board, ''a, 'b) gamespec ->
    ((term * real list) list * (term * real list) list) *
     {dimin: int,
       dimout: int,
       headeval: mlTreeNeuralNetwork.nn,
       headpoli: mlTreeNeuralNetwork.nn,
       opdict: mlTreeNeuralNetwork.opdict} *
     rlGameArithGround.board psMCTS.sit list


end
