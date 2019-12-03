signature mlReinforce =
sig

  include Abbrev

  type dhex = mlTreeNeuralNetwork.dhex
  type dhtnn = mlTreeNeuralNetwork.dhtnn
  type schedule = mlNeuralNetwork.schedule
  type dhtnn_param = mlTreeNeuralNetwork.dhtnn_param
  type 'a rlex = 'a psBigSteps.rlex
  
  (* players *)
  type splayer = (bool * dhtnn * bool * string * int)
  type dplayer =
    {playerid : string, dhtnn_param : dhtnn_param, schedule : schedule}
  type rplayer = (dhtnn * string)
  
  (* parallelization *)
  type 'a pre_extsearch =
    {
    write_target : string -> 'a -> unit,
    read_target : string -> 'a,
    write_exl : string -> 'a rlex -> unit,
    read_exl : string -> 'a rlex,
    write_splayer : string -> splayer -> unit,
    read_splayer : string -> splayer
    }

  type 'a extsearch = (splayer, 'a, bool * bool * 'a rlex) smlParallel.extspec

  (* reinforcement learning parameters *)
  type rl_param =
    {
    expname : string, 
    ex_window : int, 
    ncore_search : int, nsim : int, decay : real
    }
  
  type ('a,'b,'c) rlpreobj =
    {
    rl_param : rl_param,
    max_bigsteps : 'a -> int,
    game : ('a,'b) psMCTS.game,
    pre_extsearch : 'a pre_extsearch,
    pretobdict : (string, ('a -> term) * ('c -> 'a -> term)) Redblackmap.dict,
    precomp_dhtnn : dhtnn -> 'a -> 'c,
    dplayerl : dplayer list,
    level_targetl : int -> 'a list
    }
  
  type 'a rlobj =
    {
    rl_param : rl_param,
    extsearch : 'a extsearch,
    tobdict : (string, 'a -> term) Redblackmap.dict,
    dplayerl : dplayer list,
    write_exl : string -> 'a rlex -> unit,
    read_exl : string -> 'a rlex,
    board_compare : 'a * 'a -> order,
    level_targetl : int -> 'a list
    }
  
  val mk_extsearch : string -> ('a,'b,'c) rlpreobj -> 'a extsearch
  val mk_rlobj : ('a,'b,'c) rlpreobj -> 'a extsearch -> 'a rlobj

  (* communication files *)
  val log : 'a rlobj -> string -> unit
  val retrieve_player : 'a rlobj -> int -> rplayer

  (* phases *)
  val rl_train_sync: 
     'a rlobj -> ((int * int) * int) -> ((int * int) * int)
  val explore_standalone : (bool * bool) -> 'a rlobj -> rplayer -> 'a list -> 
     'a rlex * bool
  val rl_explore_sync: 
     'a rlobj -> ((int * int) * int) -> ((int * int) * int)
  
  (* main functions *)
  val rl_start_sync : 'a rlobj -> int -> unit
  val rl_restart_sync : 'a rlobj -> ((int * int) * int) -> unit


end
