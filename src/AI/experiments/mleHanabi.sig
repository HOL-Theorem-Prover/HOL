signature mleHanabi =
sig

  include Abbrev

  datatype color = Red | Yellow | Green | Blue | White | NoColor
  type card = int * color

  datatype move =
    Play of int
  | Discard of int
  | ColorClue of color
  | NumberClue of int

  val compare_move : (move * move) -> order
 
  type obsc = move option * card * int
  type obs = card * int
  type obsc_dict = (obsc, (card,int) Redblackmap.dict) Redblackmap.dict
  type obs_dict = (obs, (card,int) Redblackmap.dict) Redblackmap.dict
  type nn = mlNeuralNetwork.nn
  type ex = real list * real list
  type player = (obsc_dict * obs_dict) * (nn * nn)

  type board =
    {
    p1turn : bool,
    lastmove1 : move option, lastmove2: move option,
    hand1 : card vector, hand2 : card vector,
    clues1 : card vector, clues2 : card vector,
    clues : int, score : int, bombs : int,
    deck : card list, disc : card list, pile : card vector
    }
   
  val hanabi_dir : string
  val summary_dir : string ref
  val player_mem : ((obsc_dict * obs_dict) * (nn * nn)) ref

  (* encoding *)
  val compare_card : (card * card) -> order
  val random_startboard : unit -> board
  val oh_board : (obsc_dict * obs_dict) -> board -> real list
  
  (* observables *)
  val compare_obsc : (obsc * obsc) -> order
  val compare_obs : (obs * obs) -> order  
  val observe_hand : board -> (obsc * card) list * (obs * card) list
  val update_observable : 
    (board  * (obsc_dict * obs_dict)) -> (obsc_dict * obs_dict)
  val empty_obs : (obsc_dict * obs_dict)
  val print_obs : (obsc_dict * obs_dict) -> board -> int -> unit
  
  (* player *)
  val random_player : unit -> player
  
  (* guesses *)
  val guess_board : obsc_dict -> board -> board
  
  (* lookahead *)
  val lookahead : int -> player -> board -> move * ex * ex

  (* playing a game *)    
  val best_move : (obsc_dict * obs_dict) -> nn -> board -> move
  val apply_move : move -> board -> board
  val play_game : (obsc_dict * obs_dict) -> nn -> board -> int
  val play_ngame : (obsc_dict * obs_dict) -> nn -> int -> real
  val example_game : int -> player -> unit

  (* statistics *)
  val stats_player : int -> player -> unit
  val symdiff_player : int -> player ->  player -> unit
  (* reinforcement learning *)
  val rl_loop : int -> player * board * int list

  (* parallelization *)
  val extspec : (player, unit, (ex list * ex list) * int) smlParallel.extspec
  val rl_para : int -> int -> player * int list

end
