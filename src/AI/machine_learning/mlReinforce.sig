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

  type 'a extsearch = (splayer, 'a, bool * 'a rlex) smlParallel.extspec

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
    ex_window : int, ex_uniq : bool,
    ngen : int, ncore_search : int,
    nsim_start : int , nsim_explore : int, nsim_compete : int,
    decay : real
    }
  type ('a,'b) rlpreobj =
    {
    rl_param : rl_param,
    level_param : 'a level_param,
    max_bigsteps : 'a -> int,
    game : ('a,'b) psMCTS.game,
    pre_extsearch : 'a pre_extsearch,
    tobdict : (string, 'a -> term) Redblackmap.dict,
    dplayerl : dplayer list
    }
  type 'a rlobj =
    {
    rl_param : rl_param,
    level_param : 'a level_param,
    extsearch : 'a extsearch,
    tobdict : (string,'a -> term) Redblackmap.dict,
    dplayerl : dplayer list
    }

  val mk_extsearch : string -> ('a,'b) rlpreobj -> 'a extsearch
  val mk_rlobj : ('a,'b) rlpreobj -> 'a extsearch -> 'a rlobj

  (* phases *)
  val rl_train : 'a rlobj -> 'a rlex -> rplayer list
  val rl_compete : 'a rlobj -> int -> rplayer list -> (int * rplayer)
  val loop_rl_explore : 'a rlobj -> int -> bool -> rplayer ->
    'a rlex -> ('a rlex * int)

  (* main loop *)
  val cont_rl_loop : 'a rlobj -> int ->
     ('a rlex * rplayer option * int) ->  ('a rlex * rplayer option * int)
  val start_rl_loop : 'a rlobj -> ('a rlex * rplayer option * int)

end
