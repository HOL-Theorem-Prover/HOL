signature mlReinforce =
sig

  include Abbrev

  type dhex = mlTreeNeuralNetwork.dhex
  type dhtnn = mlTreeNeuralNetwork.dhtnn
  type schedule = mlTreeNeuralNetwork.schedule
  type dhtnn_param = mlTreeNeuralNetwork.dhtnn_param
  type 'a ex = 'a psBigSteps.ex

  (* object description *)
  type 'a level_param =
    {
    ntarget_compete : int, ntarget_explore : int,
    level_start : int, level_threshold : real,
    level_targetl : int -> int -> 'a list
    }
  type rl_param =
    {
    expname : string, 
    ex_window : int, ex_uniq : bool, 
    ngen : int,
    ncore_search : int, ncore_train : int
    }
  type 'a pre_extsearch = 
    {
    write_targetl : string -> 'a list -> unit,
    read_targetl : string -> 'a list,  
    write_exl : string -> 'a ex list -> unit,
    read_exl : string -> 'a ex list,
    write_player : string -> (bool * dhtnn * bool) -> unit,
    read_player : string -> (bool * dhtnn * bool)
    }
  type ('a,'b) rl_preobj =
    {
    rl_param : rl_param,
    level_param : 'a level_param,
    max_bigsteps : 'a -> int,
    game : ('a,'b) psMCTS.game,
    pre_extsearch : 'a pre_extsearch, 
    dhtnn_param : dhtnn_param,
    term_of_board : 'a -> term
    }
  type 'a extsearch =
    (bool * mlTreeNeuralNetwork.dhtnn * bool, 'a, bool * 'a ex list) 
    smlParallel.extspec
  type 'a rl_obj =
    {
    rl_param : rl_param,
    level_param : 'a level_param,
    extsearch : 'a extsearch, 
    dhtnn_param : dhtnn_param,
    term_of_board : 'a -> term
    }
  val mk_extsearch : string -> ('a,'b) rl_preobj -> 'a extsearch
  val mk_rl_obj : ('a,'b) rl_preobj -> 'a extsearch -> 'a rl_obj

  (* phases *)
  val rl_train : 'a rl_obj -> 'a ex list -> dhtnn
  val rl_compete : 'a rl_obj -> int -> dhtnn -> dhtnn -> (int * dhtnn)
  val loop_rl_explore : 'a rl_obj -> int -> bool -> dhtnn -> 
    'a ex list -> ('a ex list * int)

  (* main loop *)
  val cont_rl_loop : 'a rl_obj -> int -> 
     ('a ex list * dhtnn * int) ->  ('a ex list * dhtnn * int)
  val start_rl_loop : 'a rl_obj -> ('a ex list * dhtnn * int)

end
