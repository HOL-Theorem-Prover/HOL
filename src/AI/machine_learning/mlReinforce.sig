signature mlReinforce =
sig

  include Abbrev

  type tnn = mlTreeNeuralNetwork.tnn
  type tnnex = mlTreeNeuralNetwork.tnnex
  type tnndim = mlTreeNeuralNetwork.tnndim
  type schedule = mlNeuralNetwork.schedule
  type 'a rlex = 'a psBigSteps.rlex
  type 'a targetd = ('a, bool list) Redblackmap.dict
  (* I/O *)
  type 'a gameio =
    {write_boardl : string -> 'a list -> unit,
     read_boardl : string -> 'a list}
  val write_rlex : 'a gameio -> string -> 'a rlex -> unit
  val read_rlex : 'a gameio -> string -> 'a rlex

  (* players *)
  type splayer =
    {unib : bool, tnn : tnn, noiseb : bool, nsim : int}
  type ('a,'b)  dplayer =
    {player_from_tnn : tnn -> ('a,'b) psMCTS.player,
     tob : 'a -> term list, schedule : schedule, tnndim : tnndim}

  (* parallelization of the search *)
  type 'a es = (splayer, 'a, bool * 'a rlex) smlParallel.extspec

  (* reinforcement learning parameters *)
  type rlparam =
    {expdir : string, exwindow : int, ncore : int, ntarget : int, nsim : int}
  type ('a,'b) rlobj =
    {
    rlparam : rlparam,
    game : ('a,'b) psMCTS.game,
    gameio : 'a gameio,
    dplayer : ('a,'b) dplayer,
    infobs : 'a list -> unit
    }
  val mk_mctsobj : ('a,'b) rlobj -> splayer -> ('a,'b) psMCTS.mctsobj
  val mk_extsearch : string -> ('a,'b) rlobj -> 'a es

  (* storage *)
  val log : ('a,'b) rlobj -> string -> unit
  val store_rlex : ('a,'b) rlobj -> int -> 'a rlex -> unit
  val retrieve_rlex : ('a,'b) rlobj -> int -> 'a rlex
  val store_tnn : ('a,'b) rlobj -> int -> tnn -> unit
  val retrieve_tnn : ('a,'b) rlobj -> int -> tnn
  val store_targetd : ('a,'b) rlobj -> int -> 'a targetd -> unit
  val retrieve_targetd : ('a,'b) rlobj -> int -> 'a targetd

  (* main functions *)
  val rl_start : ('a,'b) rlobj * 'a es -> 'a targetd -> unit
  val rl_restart : int -> ('a,'b) rlobj * 'a es -> 'a targetd -> unit

  (* final testing
  type 'a ftes = (unit, 'a, bool * int * 'a option) smlParallel.extspec
  type 'a fttnnes = (tnn, 'a, bool * int * 'a option) smlParallel.extspec
  val ft_mk_extsearch : string -> ('a,'b) rlobj ->
    ('a,'b) psMCTS.player -> 'a ftes
  val fttnn_mk_extsearch : string -> ('a,'b) rlobj -> 'a fttnnes
  val fttnnbs_mk_extsearch : string -> ('a,'b) rlobj -> 'a fttnnes
  *)
end
