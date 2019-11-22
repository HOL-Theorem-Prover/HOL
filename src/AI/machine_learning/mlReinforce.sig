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
  type 'a level_param =
    {
    ntarget_start: int, ntarget_compete : int, ntarget_explore : int,
    level_start : int, level_threshold : real,
    level_targetl : int -> int -> 'a list
    }
  type rl_param =
    {
    expname : string,
    ex_window : int, ex_filter : int option,
    ngen : int, ncore_search : int,
    nsim_start : int , nsim_explore : int, nsim_compete : int,
    decay : real
    }
  type ('a,'b,'c) rlpreobj =
    {
    rl_param : rl_param,
    level_param : 'a level_param,
    max_bigsteps : 'a -> int,
    game : ('a,'b) psMCTS.game,
    pre_extsearch : 'a pre_extsearch,
    pretobdict : (string, ('a -> term) * ('c -> 'a -> term)) Redblackmap.dict,
    precomp_dhtnn : dhtnn -> 'a -> 'c,
    dplayerl : dplayer list
    }
  type 'a rlobj =
    {
    rl_param : rl_param,
    level_param : 'a level_param,
    extsearch : 'a extsearch,
    tobdict : (string, 'a -> term) Redblackmap.dict,
    dplayerl : dplayer list,
    write_exl : string -> 'a rlex -> unit,
    read_exl : string -> 'a rlex,
    board_compare : 'a * 'a -> order
    }
  val mk_extsearch : string -> ('a,'b,'c) rlpreobj -> 'a extsearch
  val mk_rlobj : ('a,'b,'c) rlpreobj -> 'a extsearch -> 'a rlobj

  (* example filtering *)
  val rl_filter_train :
    'a rlobj -> rplayer -> int -> 'a rlex -> ('a rlex * rplayer) list
  val rl_filter_compete :
    'a rlobj -> int -> ('a rlex * rplayer) list -> 'a rlex
  val rl_filter :
    'a rlobj -> rplayer -> int -> int -> 'a rlex -> 'a rlex

  (* phases *)
  val rl_train : 'a rlobj -> 'a rlex -> rplayer list
  val rl_compete : 'a rlobj -> int -> rplayer list -> (int * rplayer)
  val loop_rl_explore : int -> 'a rlobj -> int -> bool -> rplayer ->
    'a rlex -> ('a rlex * int)

  (* main loop *)
  val cont_rl_loop : 'a rlobj -> int ->
     ('a rlex * rplayer option * int) ->  ('a rlex * rplayer option * int)
  val start_rl_loop : 'a rlobj -> ('a rlex * rplayer option * int)

end
