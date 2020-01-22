signature mlReinforce =
sig

  include Abbrev

  type tnn = mlTreeNeuralNetwork.tnn
  type tnnex = mlTreeNeuralNetwork.tnnex
  type tnnparam = mlTreeNeuralNetwork.tnnparam
  type schedule = mlNeuralNetwork.schedule
  type 'a rlex = 'a psBigSteps.rlex
  
  (* I/O *)
  type 'a gameio =
    {write_boardl : string -> 'a list -> unit,
     read_boardl : string -> 'a list}
  val write_rlex : 'a gameio -> string -> 'a rlex -> unit
  val read_rlex : 'a gameio -> string -> 'a rlex

  (* players *)
  type splayer = bool * tnn * bool * int
  type 'a dplayer = 
    {tob : 'a -> term list, schedule : schedule, tnnparam : tnnparam}
  
  (* parallelization of the search *)
  type 'a es = (splayer, 'a, bool * 'a rlex) smlParallel.extspec

  (* reinforcement learning parameters *)
  type rlparam =
    {expname : string, exwindow : int, ncore : int, 
     level_threshold : real, nsim : int, decay : real}
  type ('a,'b) rlobj =
    {
    rlparam : rlparam,
    game : ('a,'b) psMCTS.game,
    gameio : 'a gameio,
    level_targetl : int -> 'a list,
    dplayer : 'a dplayer
    }
  val mk_bsobj : ('a,'b) rlobj -> splayer -> ('a,'b) psBigSteps.bsobj
  val mk_extsearch : string -> ('a,'b) rlobj -> 'a es

  (* storage *)
  val log : ('a,'b) rlobj -> string -> unit
  val store_rlex : ('a,'b) rlobj -> int -> 'a rlex -> unit  
  val retrieve_rlex : ('a,'b) rlobj -> int -> 'a rlex
  val store_tnn : ('a,'b) rlobj -> int -> tnn -> unit
  val retrieve_tnn : ('a,'b) rlobj -> int -> tnn
  
  (* main functions *)
  val rl_start : ('a,'b) rlobj * 'a es -> int -> unit
  val rl_restart : int -> ('a,'b) rlobj * 'a es -> int -> unit

end
